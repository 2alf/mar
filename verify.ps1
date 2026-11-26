<#
  Build the formalization and check the axioms of every result.

    powershell -ExecutionPolicy Bypass -File .\verify.ps1 [-MaxGB 12] [-SkipCache]

  1. lake exe cache get   (Mathlib build cache; skip with -SkipCache)
  2. lake build           (MonsterCN and MAR)
  3. lake env lean check_axioms.lean, and check that every result depends only on
     propext, Classical.choice and Quot.sound.
  Steps 2 and 3 run under a memory guard that stops any lean.exe started by this script once it
  uses more than -MaxGB GB. Logs are written to verify_logs\.
#>
param([double]$MaxGB = 12, [switch]$SkipCache)
$ErrorActionPreference = 'Continue'
$Root = $PSScriptRoot
Set-Location $Root
$Logs = Join-Path $Root 'verify_logs'
New-Item -ItemType Directory -Force -Path $Logs | Out-Null
$failed = $false

function Invoke-Guarded([string]$Name, [scriptblock]$Cmd) {
  $pre = @(Get-Process -Name lean -ErrorAction SilentlyContinue | ForEach-Object { $_.Id })
  $limit = [int64]($MaxGB * 1GB)
  $guard = Start-Job -ArgumentList $limit, (,$pre) -ScriptBlock {
    param([int64]$Limit, $Skip)
    while ($true) {
      foreach ($p in @(Get-Process -Name lean -ErrorAction SilentlyContinue)) {
        if ($Skip -contains $p.Id) { continue }
        $mem = [Math]::Max([int64]$p.WorkingSet64, [int64]$p.PrivateMemorySize64)
        if ($mem -gt $Limit) {
          'killed lean.exe PID {0} at {1:N1} GB' -f $p.Id, ($mem / 1GB)
          Stop-Process -Id $p.Id -Force -ErrorAction SilentlyContinue
        }
      }
      Start-Sleep -Seconds 2
    }
  }
  $log = Join-Path $Logs "$Name.log"
  try { & $Cmd 2>&1 | Tee-Object -FilePath $log | Out-Host; $code = $LASTEXITCODE }
  finally {
    $killed = @(Receive-Job $guard -ErrorAction SilentlyContinue)
    Stop-Job $guard; Remove-Job $guard -Force
    if (Test-Path $log) { $l = Get-Content $log; Set-Content -Path $log -Value $l -Encoding UTF8 }
  }
  if ($killed.Count -gt 0) { $killed | ForEach-Object { Write-Host $_ -ForegroundColor Red }; return 1 }
  return $code
}

if (-not $SkipCache) {
  Write-Host '=== lake exe cache get' -ForegroundColor Cyan
  & lake exe cache get
}

Write-Host "=== lake build (memory guard: $MaxGB GB per lean.exe)" -ForegroundColor Cyan
$t = Measure-Command { $rc = Invoke-Guarded 'build' { lake build } }
Write-Host ('build time: {0:N1} min' -f $t.TotalMinutes)
if ($rc -ne 0) { Write-Host 'FAILED: lake build' -ForegroundColor Red; $failed = $true }

if (-not $failed) {
  Write-Host '=== lake env lean check_axioms.lean' -ForegroundColor Cyan
  $rc = Invoke-Guarded 'axioms' { lake env lean check_axioms.lean }
  $expected = @(Get-Content (Join-Path $Root 'check_axioms.lean') | Where-Object { $_ -match '^#print axioms ' }).Count
  $allowed = @('propext', 'Classical.choice', 'Quot.sound')
  $ok = 0; $bad = @()
  foreach ($line in Get-Content (Join-Path $Logs 'axioms.log')) {
    if ($line -match "^'.+' does not depend on any axioms$") { $ok++; continue }
    if ($line -match "^'.+' depends on axioms: \[(.*)\]$") {
      $ax = @($Matches[1] -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
      if (@($ax | Where-Object { $allowed -notcontains $_ }).Count -eq 0) { $ok++ } else { $bad += $line }
    } elseif ($line -match 'error') { $bad += $line }
  }
  Write-Host "results checked: $ok of $expected"
  if ($rc -ne 0 -or $bad.Count -gt 0 -or $ok -ne $expected) {
    $bad | ForEach-Object { Write-Host $_ -ForegroundColor Red }
    Write-Host 'FAILED: axiom check' -ForegroundColor Red; $failed = $true
  }
}

if ($failed) { Write-Host 'Verification FAILED.' -ForegroundColor Red; exit 1 }
Write-Host 'Verification passed: everything builds, and every result depends only on propext, Classical.choice and Quot.sound.' -ForegroundColor Green
exit 0

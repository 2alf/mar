Conway moonshine per-class data (Co0 = 2.Co1)
=============================================

Sources (open access only)
  [DMC]  J. F. R. Duncan, S. Mack-Crane, "The moonshine module for Conway's group",
         arXiv:1409.3829v2 (LaTeX source vacogm_s1.tex, copy in sources/), published
         Forum Math. Sigma 3 (2015) e10 (open access PDF; Tables A.1/A.2 checked: same
         entries as arXiv v2 for every row inspected, including the two flagged rows).
  [D07]  J. F. R. Duncan, "Super-moonshine for Conway's largest sporadic group",
         arXiv:math/0502267v3 (LaTeX source vaco1_xr3.tex, copy in sources/).
  All the per-class data come from [DMC] Appendix A ("Data"), Table 1
  (label tab:mmdata-Tsg, "Data for the T^s_g") and Table 2 (tab:mmdata-Tsgtw).
  [D07] has NO table of groups: it treats Co1 (not Co0) acting on A^{f natural}, and
  gives only a closed formula for the traces (Theorem ThmChars, section "McKay--Thompson series").

Files
  conway_table.tsv           160 rows = the source rows of [DMC] Table 1, verbatim.
                             Columns as requested: co0_class, co1_class, order, frame_shape,
                             group_label (verbatim LaTeX), source_location, notes.
                             notes holds: plain-ASCII form of the label, chi_g, C_{-g}, the -g class,
                             merge info, flags.
  conway_table_expanded.tsv  167 rows, one per Co0 conjugacy class (merged rows like 39AB split
                             into 39A,39B; that split is mine). Extra columns: frame in TeX,
                             chi_g, C_{-g}, plain label, -g class, fixed-point-free flag, first 12
                             coefficients of T^s_g(2tau) (q^-1..q^10, computed by me from the
                             Frame shape), and SUSPECT_LABEL flag.
  conway_groups.tsv          the 134 distinct group labels -> list of Co0 classes.
  conway_twisted_table.tsv   [DMC] Table 2 (90 rows): Gamma_{g,tw} and the monster class, for
                             fixed-point-free g.
  sources/                   the two arXiv .tex sources and the parsing/check scripts.

Plain-label convention (mine; the group_label column is the source's LaTeX verbatim)
  \up\tfrac1h -> up(1/h) = [[1,1/h],[0,1]];  n\dn -> down(n) = [[1,0],[n,1]];
  juxtaposition (product) -> '*';  \vert -> '|';  X^{up(1/h)} = conjugate of X by up(1/h)
  ([DMC]: Gamma^{up 1/2} = [[1,-1/2],[0,1]] Gamma [[1,1/2],[0,1]]).

1. Definitions / normalization ([DMC])
  * eta_g(tau) := q prod_{i=1}^{24} prod_{n>0} (1 - eps_i q^n), eps_i = eigenvalues of g on
    a = Leech (x) C;  = prod_m eta(m tau)^{k_m} where the char. poly is prod_m (1-x^m)^{k_m};
    Frame shape pi_g := prod_m m^{k_m};  chi_g = tr_a(g) = k_1.
  * Conway-Norton/Queen: t_g(tau) := eta_g(tau)/eta_g(2tau) = q^{-1} prod_{n>0} prod_i (1 - eps_i q^{2n-1})
    = q^{-1} - chi_g + O(q); it is a principal modulus for genus-0 Gamma_g containing some Gamma_0(N).
  * T^s_g(tau) := str_{V^{s natural}} ghat q^{L(0)-c/24}   (SUPER trace, c = 12, q = e^{2 pi i tau}),
    i.e. T^s_g(tau) = q^{-1/2} sum_{n>=0} str_{V^{s natural}_{n/2}} g q^{n/2}.
    Variable: powers of q^{1/2}. Theorem: T^s_g(tau) = t_g(tau/2) + chi_g
      = q^{-1/2} prod_{n>0} prod_i (1 - eps_i q^{n-1/2}) + chi_g,
    and T^s_g(2tau) = t_g(tau) + chi_g = q^{-1} + O(q) is THE normalized principal modulus for Gamma_g.
  * IMPORTANT for indexing: the table's Gamma_g is the invariance group of T^s_g(2tau) (= of t_g).
    Appendix text says "Gamma_g for the invariance group of T^s_g", but the intro states
    "T^s_g(2tau) is the unique normalized principal modulus attached to the genus zero group
    Gamma_g", and e.g. 1A -> "2-" (Gamma_0(2)) only makes sense for T^s_g(2tau).
  * Coefficients: V^{s natural}_{1/2} = 0 (characterization: deg v != 1/2), so the q^0 term of
    T^s_g(2tau) is 0 (the 24-dim rep only enters t_g, as -chi_g). From the construction
    V^{s nat} = A(a)^0 (+) A(a)_tw^1: V_1 = A(a)_1 ~ so(a) = Lambda^2(24) (276, stated in [DMC] sec 3.1);
    V_{3/2} = lowest piece of A(a)_tw^1, 2048-dim, odd, so coefficient of q^2 in T^s_g(2tau) is
    -tr_{V_{3/2}}(g)  (my reading of the construction; [DMC] does not decompose it into Co0 irreps).
    Check: T^s_e(2tau) = q^-1 + 276 q - 2048 q^2 + 11202 q^3 - 49152 q^4 + ... (= monster T_2B,
    which [DMC] displays as q^-1 + 276q - 2048q^2 + ...).
  * Explicit formula ([DMC] sec 4.3, Lemma lem:moon:mtseries-gddtracefns, eqn trxVU): str_{V^{s nat}} x q^{L0-c/24} = 1/2( eta_xbar(tau/2)/eta_xbar(tau)
    + eta_{-xbar}(tau/2)/eta_{-xbar}(tau) + C_x eta_xbar(tau) - C_{z x} eta_{-xbar}(tau) ),
    C_x = str_CM x (CM = 4096-dim Clifford module); column "C_{-g}" of Table 1 is C_{hat(-g)}.
  * Twisted series T^s_{g,tw} (Table 2): constant = -chi_g if g has a fixed point on Leech,
    otherwise a principal modulus (Gamma_{g,tw} listed with a monster class).
  * [D07] (Co1, not Co0): ordinary trace "tr" on A^{f nat}; phi(tau)=eta(tau/2)/eta(tau);
    tr_{A^{f nat}} g q^{L0-c/24} = 1/2(phi_g + phi_{-g}) + 1/2(chi_G(g) eta_{-g} + chi_G(-g) eta_g),
    chi_G = chi_1+chi_24+chi_276+chi_2024+chi_1771 (trace on CM(l)_G; CM(l)_G^0 = (A^{f nat})_{3/2});
    graded dim q^{-1/2}(1 + 276 q + 2048 q^{3/2} + ...). [DMC] says these T^f_g are generally NOT
    principal moduli.

2. Counts
  * Table 1 rows: 160.  Co0 classes covered: 167 (= all of Co0), because 7 rows carry two class
    letters: 22BC, 23AB, 46AB, 39AB, 78AB, 40AB, 56AB.
  * Co1 labels in the table: 99, i.e. 101 Co1 classes (23AB, 39AB are Co1 pairs).
    Co1 classes with a single Co0 row: 38 (35 with g ~ -g, plus 22A, 40A, 28B whose two lifts are
    merged in rows 22BC, 40AB, 56AB); the other 61 Co1 labels have a +/- pair of rows.
  * Distinct group labels: 134 (verbatim and after normalization of \left( and whitespace).
    Distinct functions T^s_g (computed to q^148 from the Frame shapes): 134.
    Labels shared by several rows: 4- {2B,2C}; 8- {4D,4E,4F}; 12+12 {6E,6J}; (12+12)^{up(1/2)} {6F,6I};
    12+3*up(1/2) {6G,6H}; 12+3 {6K,6L}; 12- {6M,6N,12E*}; 16- {8F,8G,8H}; 20+20 {10D,10I};
    (20+20)^{up(1/2)} {10E,10H}; 20+5*up(1/2) {10F,10G}; 24+3*up(1/2) {12K,12N,12O};
    (24|2+12)^{up(1/4)} {12L,12M}; 28+7 {14C,14D}; 36+36 {18D,18G}; (36+36)^{up(1/2)} {18E,18F};
    36+9*up(1/2) {18H,18I}; (40|2+20)^{up(1/4)} {20F,20G}; (48|4+12)^{up(1/8)} {24I,24J};
    60+12,15,20 {30F,30J*,30K}; 60+3*up(1/2),5*up(1/2),15 {30H,30I}; (+ merged AB rows).
  * Fixed-point-free classes: 95 Co0 classes = 90 rows of Table 2 (all consistent with Frame shapes).

3. Parsing / consistency checks (all automatic, scripts in sources/)
  * Every Frame shape has degree sum m k_m = 24; element order from Frame shape (lcm of eigenvalue
    orders) equals the numeric prefix of the Co0 class name for all 160 rows.
  * Every T^s_g(2tau) has leading q^-1 and zero constant term (checks T^s_g(2tau)=t_g+chi_g).
  * [DMC] rule Gamma_{-g} = Gamma_g^{up(1/2)} ("since the Fourier expansions of T^s_g(2tau) and
    T^s_{-g}(2tau) differ exactly by signs on even powers of q"): verified on q-expansions for all
    61 pairs; for all single-row classes the even coefficients vanish.
  * Table 2 rows agree with Table 1 (same Co1 class and Frame shape) and are exactly the
    fixed-point-free rows.
  * TWO SUSPECT LABELS (transcribed verbatim, flagged SUSPECT_LABEL):
      12E (Co1 12B, 2^2 12^4/4^4 6^2): source "12-". Its T^s(2tau) = q^-1 - 2q + 5q^3 - 8q^5 + ...
        differs from T^s_{6M}=T^s_{6N} (also "12-", = q^-1 + 2q + q^3 - 2q^7 ..., which is the Gamma_0(12)
        Hauptmodul eta(4t)^4eta(6t)^2/(eta(2t)^2eta(12t)^4)), and equals T^s_{12L}=T^s_{12M}, labelled
        (24|2+12)^{up(1/4)}. Two different normalized Hauptmoduln for one group is impossible, so the
        12E entry is presumably a slip (Table 2 also lists Gamma_{12E,tw} = 12-).
      30J (Co1 30E): source "60+12,15,20", same as its partner 30K = -30J, but T^s_{30J} != T^s_{30K};
        T^s_{30J} = T^s_{30G}, labelled (60+12,15,20)^{up(1/2)}. Presumably a slip.
    With these two corrections the label partition and the function partition coincide exactly
    (134 = 134). The published FMS version has the same two entries.
  * The C_{-g} column and Table 2 columns C_g, M were transcribed but not independently verified.
  * Co0 class names are [DMC]'s own (letters ordered within each order); I did not check them
    against GAP/ATLAS 2.Co1 names.

4. Power maps / eigencharacters / same T_g / uniqueness  (what [DMC] and [D07] actually state)
  * Power maps: NOT stated anywhere in [DMC] or [D07]; no power-map columns in the tables.
  * Eigencharacter rule T(tau+1/h) = zeta T(tau): NOT stated. The only translation relation is
    Gamma_{-g} = Gamma_g^{up(1/2)} (conjugation by tau -> tau + 1/2), i.e. T^s_{-g}(2tau) is
    T^s_g(2tau) with the even-power coefficients negated. The "n|h" notation follows
    Conway-Norton / Ford-McKay-Norton ("More on replicable functions", 1994): n|h- is the index-h
    subgroup of Gamma_0(n/h) from Conway-Norton; extra notation: 12+3 up(1/2) = <Gamma_0(12), W_3*up(1/2)>
    (= 12+3' in FMN); 4|2- = 8+up(1/2)4down; 8|2+ = 16+16,up(1/2)8down.
    [DMC] says its notation differs "in certain cases" from Kondo (J. Math. Soc. Japan 37 (1985)),
    where the groups Gamma_g were first completely described.
  * Same T_g: no explicit list; it follows from the stated uniqueness of the normalized principal
    modulus (intro: "Such a function T_Gamma ... is unique") that rows with the same Gamma_g have
    the same T^s_g; [DMC] also notes "Gamma_g and Gamma_{-g} are related by conjugation".
  * Uniqueness / rigidity: [DMC] proves (Thm "uniq") V^{s nat} is the unique C2-cofinite rational
    SVOA of CFT type with c=12, self-dual, no degree-1/2 vectors; Prop.: a copy of Co0 in SO(24)
    has a unique lift to Spin(24); unique Co1-invariant N=1 element. [D07]: A^{f nat} characterized
    as N=1 SVOA (self-dual, rank 12, trivial degree-1/2 space), Aut = Co1. NO statement anywhere
    about uniqueness/rigidity of the assignment g -> Gamma_g itself (beyond the formula determining it).
    [DMC] notes that T^s_g are recovered as normalized Rademacher sums for Gamma_g, and lists a
    Rademacher-sum characterization of the T^s_g (analogue of Duncan-Frenkel Thm 6.5.1) as an
    open problem.

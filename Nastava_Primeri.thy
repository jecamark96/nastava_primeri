theory Nastava_Primeri
  imports Complex_Main
begin

text ‹
  Prateci kod za rad
  "Uloga interaktivnih dokazivaca teorema u nastavi na primerima Matematicke analize".

  Napomena: neke leme namerno sadrze @{command sorry} (dokazne obaveze koje
  NE MOGU biti dokazane pod datim pretpostavkama) ili se zavrsavaju sa
  @{command oops}. U interaktivnom radu (Isabelle/jEdit) to je dozvoljeno;
  za paketnu proveru (isabelle build) potrebna je opcija quick_and_dirty.
›

(* ========================================================================= *)
section ‹Primer 1: primena teoreme za koju nisu ispunjeni uslovi›
(* ========================================================================= *)

text ‹Bibliotecka tvrdjenja na koja se pozivamo (stampaju se komandom thm).›

thm MVT
thm continuous_at_imp_continuous_on
thm DERIV_isCont
thm continuous_on_subset
thm real_differentiable_def
thm DERIV_unique

subsection ‹Struktura dokaza: prazan i neprazan slucaj (proof (cases ...))›

text ‹Ako bismo zeleli da razdvojimo prazan i neprazan domen, to se
  najcitljivije zapisuje ovako. Kao sto se vidi nize, ovo razdvajanje
  zapravo nije potrebno: za prazan D tvrdjenje ∀x∈D. ... vazi trivijalno.›

lemma student_proof_cases_skeleton:
  fixes f :: "real ⇒ real"
    and D :: "real set"
  assumes der: "⋀x. x ∈ D ⟹ DERIV f x :> 0"
  shows "∀x∈D. ∀y∈D. f x = f y"
proof (cases "∃x. x ∈ D")
  case True
  show ?thesis
    sorry
next
  case False
  show ?thesis
    using False by auto
qed

subsection ‹Struktura dokaza: bez gubitka opstosti x < y›

text ‹Tacke x i y se ne biraju, vec su date (univerzalno kvantifikovane).
  Slucaj x = y je trivijalan, a slucajevi x < y i y < x su simetricni,
  pa je dovoljno razmotriti x < y.›

lemma student_proof_wlog_skeleton:
  fixes f :: "real ⇒ real"
    and D :: "real set"
  assumes der: "⋀x. x ∈ D ⟹ DERIV f x :> 0"
  shows "∀x∈D. ∀y∈D. f x = f y"
proof -
  have "∀x∈D. ∀y∈D. x < y ⟶ f x = f y"
  proof safe
    fix x y
    assume "x ∈ D" "y ∈ D" "x < y"
    show "f x = f y"
      sorry
  qed
  then show ?thesis
    by (smt (verit))
qed

subsection ‹Primena MVT: tri dokazne obaveze›

lemma mvt_obligations_skeleton:
  fixes f :: "real ⇒ real"
    and x y :: real
  assumes "x < y"
  shows "∃l c. x < c ∧ c < y ∧ DERIV f c :> l ∧ f y - f x = (y - x) * l"
proof (rule MVT)
  show "x < y" by fact
next
  show "continuous_on {x..y} f"
    sorry
next
  fix t
  assume "x < t" "t < y"
  show "f differentiable at t"
    sorry
qed

subsection ‹Najbolji pokusaj za proizvoljan skup D: ostaju tri ista problema›

text ‹Sva tri preostala sorry iskaza traze isto: da tacke izmedju x i y
  pripadaju skupu D. To iz pretpostavki ne sledi.›

lemma student_proof:
  fixes f :: "real ⇒ real"
    and D :: "real set"
  assumes der: "⋀x. x ∈ D ⟹ DERIV f x :> 0"
  shows "∀x∈D. ∀y∈D. f x = f y"
proof -
  have "∀x∈D. ∀y∈D. x < y ⟶ f x = f y"
  proof safe
    fix x y
    assume "x ∈ D" "y ∈ D" "x < y"
    have mvt: "∃l c. x < c ∧ c < y ∧
                     DERIV f c :> l ∧
                     f y - f x = (y - x) * l"
    proof (rule MVT)
      show "x < y" by fact
    next
      show "continuous_on {x..y} f"
      proof -
        have contD: "continuous_on D f"
        proof (rule continuous_at_imp_continuous_on, rule ballI)
          fix t
          assume tD: "t ∈ D"
          show "isCont f t"
            by (rule DERIV_isCont[OF der[OF tD]])
        qed
        moreover have "{x..y} ⊆ D"
          sorry  ― ‹problem 1›
        ultimately show ?thesis
          by (rule continuous_on_subset)
      qed
    next
      fix t
      assume "x < t" "t < y"
      then have "t ∈ D"
        sorry  ― ‹problem 2›
      then show "f differentiable at t"
        using der[of t]
        by (auto simp add: real_differentiable_def)
    qed
    then obtain l c where
      mvt: "x < c" "c < y" "(f has_real_derivative l) (at c)" "f y - f x = (y - x) * l"
      by auto
    have "c ∈ D"
      sorry  ― ‹problem 3›
    then have "l = 0"
      using DERIV_unique der mvt(3)
      by fastforce
    then show "f x = f y"
      using mvt(4)
      by auto
  qed
  then show ?thesis
    by (smt (verit))
qed

subsection ‹Kada je domen segment [a, b], dokaz prolazi u celosti›

lemma student_proof_interval:
  fixes f :: "real ⇒ real"
    and a b :: "real"
  assumes der: "⋀x. x ∈ {a..b} ⟹ DERIV f x :> 0"
  shows "∀x∈{a..b}. ∀y∈{a..b}. f x = f y"
proof -
  have "∀x∈{a..b}. ∀y∈{a..b}. x < y ⟶ f x = f y"
  proof safe
    fix x y
    assume "x ∈ {a..b}" "y ∈ {a..b}" "x < y"
    have mvt: "∃l c. x < c ∧ c < y ∧
                     DERIV f c :> l ∧
                     f y - f x = (y - x) * l"
    proof (rule MVT)
      show "x < y" by fact
    next
      show "continuous_on {x..y} f"
      proof -
        have contD: "continuous_on {a..b} f"
        proof (rule continuous_at_imp_continuous_on, rule ballI)
          fix t
          assume tD: "t ∈ {a..b}"
          show "isCont f t"
            by (rule DERIV_isCont[OF der[OF tD]])
        qed
        moreover have "{x..y} ⊆ {a..b}"
          using ‹x ∈ {a..b}› ‹y ∈ {a..b}›
          by auto
        ultimately show ?thesis
          by (rule continuous_on_subset)
      qed
    next
      fix t
      assume "x < t" "t < y"
      then have "t ∈ {a..b}"
        using ‹x ∈ {a..b}› ‹y ∈ {a..b}›
        by auto
      then show "f differentiable at t"
        using der[of t]
        by (auto simp add: real_differentiable_def)
    qed
    then obtain l c where
      mvt: "x < c" "c < y" "(f has_real_derivative l) (at c)" "f y - f x = (y - x) * l"
      by auto
    have "c ∈ {a..b}"
      using mvt(1-2) ‹x ∈ {a..b}› ‹y ∈ {a..b}›
      by auto
    then have "l = 0"
      using DERIV_unique der mvt(3)
      by fastforce
    then show "f x = f y"
      using mvt(4)
      by auto
  qed
  then show ?thesis
    by (smt (verit))
qed

subsection ‹Opstije: dovoljno je da D bude interval›

text ‹Pretpostavka ‹interval› tacno izrazava ono sto je nedostajalo:
  sa svakim dvema tackama skup D sadrzi i sve tacke izmedju njih.›

lemma constant_on_interval:
  fixes f :: "real ⇒ real"
    and D :: "real set"
  assumes der: "⋀x. x ∈ D ⟹ DERIV f x :> 0"
    and interval: "⋀x y z. x ∈ D ⟹ y ∈ D ⟹ x ≤ z ⟹ z ≤ y ⟹ z ∈ D"
  shows "∀x∈D. ∀y∈D. f x = f y"
proof -
  have "∀x∈D. ∀y∈D. x < y ⟶ f x = f y"
  proof safe
    fix x y
    assume xD: "x ∈ D" and yD: "y ∈ D" and "x < y"
    have mvt: "∃l c. x < c ∧ c < y ∧
                     DERIV f c :> l ∧
                     f y - f x = (y - x) * l"
    proof (rule MVT)
      show "x < y" by fact
    next
      show "continuous_on {x..y} f"
      proof -
        have contD: "continuous_on D f"
        proof (rule continuous_at_imp_continuous_on, rule ballI)
          fix t
          assume tD: "t ∈ D"
          show "isCont f t"
            by (rule DERIV_isCont[OF der[OF tD]])
        qed
        moreover have "{x..y} ⊆ D"
        proof
          fix z
          assume "z ∈ {x..y}"
          then show "z ∈ D"
            using interval[OF xD yD] by auto
        qed
        ultimately show ?thesis
          by (rule continuous_on_subset)
      qed
    next
      fix t
      assume "x < t" "t < y"
      then have "t ∈ D"
        using interval[OF xD yD, of t] by (meson less_imp_le)
      then show "f differentiable at t"
        using der[of t]
        by (auto simp add: real_differentiable_def)
    qed
    then obtain l c where
      mvt: "x < c" "c < y" "(f has_real_derivative l) (at c)" "f y - f x = (y - x) * l"
      by auto
    have "c ∈ D"
      using interval[OF xD yD, of c] mvt(1,2) by (meson less_imp_le)
    then have "l = 0"
      using DERIV_unique der mvt(3)
      by fastforce
    then show "f x = f y"
      using mvt(4)
      by auto
  qed
  then show ?thesis
    by (smt (verit))
qed


(* ========================================================================= *)
section ‹Primer 2: neopravdano poistovecivanje egzistencijalnih svedoka›
(* ========================================================================= *)

subsection ‹Sta se desava kada se novi svedok uvede pod starim imenom›

text ‹Pretpostavka je oslabljena uslovom a ≤ b: bez njega bi bila
  protivrecna (za a > b segment {a..b} je prazan), pa bi se False moglo
  dokazati direktno iz nje, sto bi pokvarilo primer.

  Posle drugog obtain, cinjenica 1 i dalje govori o PRVOM c; sistem tu
  staru, sada nedostupnu promenljivu prikazuje pod izmenjenim imenom.
  Zato iz 1 i 2 ne sledi False: to su dve razlicite tacke.›

lemma
  assumes "⋀a b::real. a ≤ b ⟹ ∃x. x ∈ {a..b}"
  shows "False"
proof -
  obtain c::real where 1: "c ∈ {0..1}"
    using assms[of 0 1]
    by auto

  obtain c::real where 2: "c ∈ {2..3}"
    using assms[of 2 3]
    by auto

  note 1  ― ‹pogledati u izlazu kako je prikazano staro c›

  show False
    using 1 2
    sorry  ― ‹nije dokazivo: 1 i 2 govore o razlicitim tackama›
qed

subsection ‹Studentov pokusaj dokaza Lagranzove teoreme›

text ‹Dve (ispravne) primene Rolove teoreme modelujemo pretpostavkama
  r1 i r2; f' oznacava izvod. Prvi obtain daje tacku iz (a, d), drugi
  tacku iz (d, b). Pravilo eliminacije egzistencijalnog kvantifikatora
  (exE) zahteva da svedok bude NOVA promenljiva; zato drugi svedok ne
  moze biti isti kao prvi, cak ni kada nosi isto ime.›

thm exE

lemma lagrange_student_attempt:
  fixes f f' :: "real ⇒ real"
    and a b d :: real
  assumes "a < d" "d < b"
    and r1: "∃c. a < c ∧ c < d ∧ f d - f a = f' c * (d - a)"
    and r2: "∃c. d < c ∧ c < b ∧ f b - f d = f' c * (b - d)"
  shows "∃c. a < c ∧ c < b ∧ f b - f a = f' c * (b - a)"
proof -
  obtain c where c1: "a < c" "c < d" "f d - f a = f' c * (d - a)"
    using r1 by blast
  obtain c where c2: "d < c" "c < b" "f b - f d = f' c * (b - d)"
    using r2 by blast
  have "f b - f a = f' c * (b - a)"
    sorry  ― ‹studentov korak: nije opravdan›
  moreover have "a < c"
    using ‹a < d› c2(1) by linarith
  ultimately show ?thesis
    using c2(2) by blast
qed

text ‹Kada svedoke imenujemo razlicito, vidi se sta se zaista dobija.›

lemma lagrange_student_attempt_honest:
  fixes f f' :: "real ⇒ real"
    and a b d :: real
  assumes "a < d" "d < b"
    and r1: "∃c. a < c ∧ c < d ∧ f d - f a = f' c * (d - a)"
    and r2: "∃c. d < c ∧ c < b ∧ f b - f d = f' c * (b - d)"
  shows "∃c1 c2. c1 < c2 ∧ f b - f a = f' c1 * (d - a) + f' c2 * (b - d)"
proof -
  obtain c1 where c1: "a < c1" "c1 < d" "f d - f a = f' c1 * (d - a)"
    using r1 by blast
  obtain c2 where c2: "d < c2" "c2 < b" "f b - f d = f' c2 * (b - d)"
    using r2 by blast
  have "c1 < c2"
    using c1(2) c2(1) by linarith
  moreover have "f b - f a = f' c1 * (d - a) + f' c2 * (b - d)"
    using c1(3) c2(3) by linarith
  ultimately show ?thesis
    by blast
qed


(* ========================================================================= *)
section ‹Primer 3: zamena mesta kvantifikatorima (uniformna neprekidnost)›
(* ========================================================================= *)

definition student_delta :: "real ⇒ real ⇒ real" where
  "student_delta e x = min 1 (e / (2 * ¦x¦ + 1))"

subsection ‹Deo studentovog racuna koji jeste ispravan›

lemma student_delta_positive:
  fixes e x :: real
  assumes epos: "0 < e"
  shows "0 < student_delta e x"
proof -
  have pos: "0 < 2 * ¦x¦ + 1"
    using abs_ge_zero[of x] by linarith
  have "0 < e / (2 * ¦x¦ + 1)"
    using epos pos by (rule divide_pos_pos)
  then show ?thesis
    unfolding student_delta_def by simp
qed

lemma student_delta_works_at_fixed_x:
  fixes e x y :: real
  assumes epos: "0 < e"
      and close: "dist y x < student_delta e x"
  shows "dist (y^2) (x^2) < e"
proof -
  have pos: "0 < 2 * ¦x¦ + 1"
    using abs_ge_zero[of x] by linarith
  have h1: "¦y - x¦ < 1" and h2: "¦y - x¦ < e / (2 * ¦x¦ + 1)"
    using close by (simp_all add: student_delta_def dist_real_def)
  have h2': "¦y - x¦ * (2 * ¦x¦ + 1) < e"
    using h2 by (simp add: pos_less_divide_eq[OF pos])
  have hy: "¦y¦ ≤ ¦x¦ + 1"
  proof -
    have "x + (y - x) = y"
      by linarith
    then have "¦y¦ ≤ ¦x¦ + ¦y - x¦"
      using abs_triangle_ineq[of x "y - x"] by simp
    then show ?thesis
      using h1 by linarith
  qed
  have "¦y + x¦ ≤ 2 * ¦x¦ + 1"
    using abs_triangle_ineq[of y x] hy by linarith
  then have "¦y - x¦ * ¦y + x¦ ≤ ¦y - x¦ * (2 * ¦x¦ + 1)"
    by (rule mult_left_mono) simp
  moreover have "dist (y^2) (x^2) = ¦y - x¦ * ¦y + x¦"
  proof -
    have "y^2 - x^2 = (y - x) * (y + x)"
      by algebra
    then show ?thesis
      by (simp add: dist_real_def abs_mult)
  qed
  ultimately show ?thesis
    using h2' by linarith
qed

subsection ‹Dokazana je tackasta neprekidnost›

theorem what_the_student_actually_proved:
  "∀x::real. ∀e>0. ∃d>0. ∀y.
      dist y x < d ⟶ dist (y^2) (x^2) < e"
proof (intro allI impI)
  fix x e :: real
  assume epos: "0 < e"
  show "∃d>0. ∀y. dist y x < d ⟶ dist (y^2) (x^2) < e"
  proof (rule exI[where x = "student_delta e x"], intro conjI allI impI)
    show "0 < student_delta e x"
      using epos by (rule student_delta_positive)
  next
    fix y
    assume "dist y x < student_delta e x"
    with epos show "dist (y^2) (x^2) < e"
      by (rule student_delta_works_at_fixed_x)
  qed
qed

subsection ‹Neuniformnost: studentovo delta tezi nuli kada |x| raste›

text ‹Za epsilon = 1 je student_delta 1 x ≤ 1 / (2|x| + 1), pa za
  x = 1/d dobijamo vrednost manju od proizvoljnog d > 0. Zato ne postoji
  pozitivan broj koji je manji ili jednak svim vrednostima student_delta 1 x.›

lemma student_delta_tends_to_zero:
  fixes d :: real
  assumes dpos: "0 < d"
  shows "∃x. student_delta 1 x < d"
proof -
  define x where "x = 1 / d"
  have dnz: "d ≠ 0"
    using dpos by (metis less_irrefl)
  have xpos: "0 < x"
    using dpos unfolding x_def by simp
  have dx: "d * x = 1"
    using dnz unfolding x_def by simp
  have ax: "¦x¦ = x"
    using xpos by (rule abs_of_pos)
  have pos: "0 < 2 * ¦x¦ + 1"
    using abs_ge_zero[of x] by linarith
  have "d * (2 * ¦x¦ + 1) = 2 * (d * x) + d"
    unfolding ax by algebra
  then have big: "1 < d * (2 * ¦x¦ + 1)"
    using dx dpos by linarith
  have "1 / (2 * ¦x¦ + 1) < d"
    using big by (simp add: pos_divide_less_eq[OF pos])
  moreover have "student_delta 1 x ≤ 1 / (2 * ¦x¦ + 1)"
    unfolding student_delta_def by simp
  ultimately have "student_delta 1 x < d"
    by linarith
  then show ?thesis
    by blast
qed

subsection ‹Eksplicitni kontraprimer: za svako d > 0 postoje bliske tacke
  u kojima se kvadrati razlikuju bar za 1›

text ‹Za d > 0 uzimamo x = 1/d i y = 1/d + d/2. Tada je |x - y| = d/2 < d,
  a y^2 - x^2 = (y - x)(y + x) = d/2 * (2/d + d/2) = 1 + d^2/4 ≥ 1.
  U formalnom zapisu stavljamo h = d/2, pa je x = 1/(2h) i y = x + h.›

lemma counterexample_for_every_positive_delta:
  fixes d :: real
  assumes dpos: "0 < d"
  shows "∃x y::real.
      dist x y < d ∧ 1 ≤ dist (x^2) (y^2)"
proof -
  define h where "h = d / 2"
  define x where "x = 1 / (2 * h)"
  define y where "y = x + h"
  have hpos: "0 < h"
    using dpos unfolding h_def by linarith
  have hnz: "h ≠ 0"
    using hpos by (metis less_irrefl)
  have hx: "2 * h * x = 1"
    using hnz unfolding x_def by simp
  have "x - y < d" "- (x - y) < d"
    using dpos unfolding y_def h_def by linarith+
  then have close: "dist x y < d"
    by (simp add: dist_real_def abs_less_iff)
  have "y^2 - x^2 = 2 * h * x + h^2"
    unfolding y_def by algebra
  also have "… = 1 + h^2"
    using hx by linarith
  finally have diff: "y^2 - x^2 = 1 + h^2" .
  have "- (x^2 - y^2) ≤ ¦x^2 - y^2¦"
    by (rule abs_ge_minus_self)
  then have "y^2 - x^2 ≤ dist (x^2) (y^2)"
    by (simp add: dist_real_def)
  moreover have "0 ≤ h^2"
    by (rule zero_le_power2)
  ultimately have "1 ≤ dist (x^2) (y^2)"
    using diff by linarith
  with close show ?thesis
    by blast
qed

theorem student_delta_is_not_a_uniform_witness:
  "∀x0::real. ∃x y::real.
      dist x y < student_delta 1 x0 ∧
      1 ≤ dist (x^2) (y^2)"
proof
  fix x0 :: real
  have "0 < student_delta 1 x0"
    by (rule student_delta_positive) simp
  then show "∃x y::real. dist x y < student_delta 1 x0 ∧ 1 ≤ dist (x^2) (y^2)"
    by (rule counterexample_for_every_positive_delta)
qed

theorem no_uniform_delta_for_epsilon_one:
  "¬ (∃d>0. ∀x y::real.
      dist x y < d ⟶ dist (x^2) (y^2) < 1)"
proof
  assume "∃d>0. ∀x y::real. dist x y < d ⟶ dist (x^2) (y^2) < 1"
  then obtain d :: real where dpos: "0 < d"
    and unif: "∀x y::real. dist x y < d ⟶ dist (x^2) (y^2) < 1"
    by blast
  obtain x y :: real where xy: "dist x y < d" and big: "1 ≤ dist (x^2) (y^2)"
    using counterexample_for_every_positive_delta[OF dpos] by blast
  have "dist (x^2) (y^2) < 1"
    using unif xy by blast
  with big show False
    by linarith
qed

subsection ‹Studentova tvrdnja nije tacna›

theorem student_claim_is_false:
  "¬ uniformly_continuous_on (UNIV :: real set) (λx. x^2)"
proof
  assume "uniformly_continuous_on (UNIV :: real set) (λx. x^2)"
  then have "∃d>0. ∀x∈(UNIV::real set). ∀x'∈(UNIV::real set).
               dist x' x < d ⟶ dist (x'^2) (x^2) < 1"
    unfolding uniformly_continuous_on_def
    using zero_less_one by blast
  then have "∃d>0. ∀x y::real. dist x y < d ⟶ dist (x^2) (y^2) < 1"
    by blast
  with no_uniform_delta_for_epsilon_one show False
    by blast
qed

subsection ‹Ispravna, oslabljena verzija: segment [-M, M]›

theorem square_uniformly_continuous_on_symmetric_interval_explicit:
  fixes M :: real
  assumes M_nonnegative: "0 ≤ M"
  shows "uniformly_continuous_on {-M..M} (λx::real. x^2)"
  unfolding uniformly_continuous_on_def
proof (intro allI impI)
  fix e :: real
  assume epos: "0 < e"
  have pos: "0 < 2 * M + 1"
    using M_nonnegative by linarith
  define d where "d = e / (2 * M + 1)"
  have dpos: "0 < d"
    unfolding d_def using epos pos by (rule divide_pos_pos)
  show "∃d>0. ∀x∈{-M..M}. ∀x'∈{-M..M}. dist x' x < d ⟶ dist (x'^2) (x^2) < e"
  proof (rule exI[where x = d], intro conjI ballI impI)
    show "0 < d" by (rule dpos)
  next
    fix x x' :: real
    assume xM: "x ∈ {-M..M}" and x'M: "x' ∈ {-M..M}" and close: "dist x' x < d"
    from xM have x1: "-M ≤ x" "x ≤ M" by auto
    from x'M have x2: "-M ≤ x'" "x' ≤ M" by auto
    have "x' + x ≤ 2 * M + 1" "- (x' + x) ≤ 2 * M + 1"
      using x1 x2 by linarith+
    then have sum: "¦x' + x¦ ≤ 2 * M + 1"
      by (simp add: abs_le_iff)
    have "¦x' - x¦ < e / (2 * M + 1)"
      using close by (simp add: dist_real_def d_def)
    then have diff: "¦x' - x¦ * (2 * M + 1) < e"
      by (simp add: pos_less_divide_eq[OF pos])
    have "dist (x'^2) (x^2) = ¦x' - x¦ * ¦x' + x¦"
    proof -
      have "x'^2 - x^2 = (x' - x) * (x' + x)"
        by algebra
      then show ?thesis
        by (simp add: dist_real_def abs_mult)
    qed
    also have "… ≤ ¦x' - x¦ * (2 * M + 1)"
      using sum by (rule mult_left_mono) simp
    also have "… < e"
      by (rule diff)
    finally show "dist (x'^2) (x^2) < e" .
  qed
qed


(* ========================================================================= *)
section ‹Primer 4: pronalazenje kontraprimera i modela›
(* ========================================================================= *)

lemma wrong_maximum_sum:
  fixes f g :: "real ⇒ real"
  shows
    "max (f 0 + g 0) (f 1 + g 1) =
     max (f 0) (f 1) + max (g 0) (g 1)"
  quickcheck [exhaustive, size = 4, timeout = 30,
              eval = "(f 0, f 1, g 0, g 1)"]
  oops

definition f :: "real ⇒ real ⇒ real" where
  "f b x = x^2 + b*x"

lemma rolle_model:
  fixes b c :: real
  shows
    "0 < c ∧ c < 1 ∧
     f b 0 = f b 1 ∧
     2*c + b = 0"
  nitpick [satisfy, timeout = 30,
           max_potential = 0,
           eval = "(b,c)"]
  oops

text ‹Provera pronadjenog modela b = -1, c = 1/2.›

lemma rolle_model_check:
  "0 < (1/2::real) ∧ (1/2::real) < 1 ∧ f (-1) 0 = f (-1) 1 ∧ 2*(1/2) + (-1::real) = 0"
  by (simp add: f_def)

end

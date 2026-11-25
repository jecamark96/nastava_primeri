theory Prva_teorija
imports Main Complex_Main 
begin

(*odsecak realne prave*)
definition odsecak :: "real ⇒ real ⇒ real set" where
  "odsecak a b = {x::real. a ≤ x ∧ x ≤ b}"

type_synonym realni_niz = "nat ⇒ real"

definition niz_odsecaka
  :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ nat ⇒ real set"
  where "niz_odsecaka a b n = odsecak (a n) (b n)"

definition umetnuti_odsecci1
  :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ bool"
where
  "umetnuti_odsecci1 a b ⟷
    (∀n. a n ≤ b n) ∧
    (∀n. niz_odsecaka a b (Suc n) ⊆ niz_odsecaka a b n)"

definition umetnuti_odsecci2 :: "(nat ⇒ real set) ⇒ bool" where
  "umetnuti_odsecci2 J ⟷
    (∀n. ∃a b. a ≤ b ∧ J n = odsecak a b) ∧
    (∀n. J (Suc n) ⊆ J n)"


lemma l3_3_1_krajevi:
  fixes a b :: "nat ⇒ real"
  assumes neprazni: "⋀n. a n ≤ b n"
      and levi: "⋀m n. m ≤ n ⟹ a m ≤ a n"
      and desni: "⋀m n. m ≤ n ⟹ b n ≤ b m"
  shows "∃x. ∀n. a n ≤ x ∧ x ≤ b n"
proof -
  have svi_krajevi: "a m ≤ b n" for m n
  proof -
    have "a m ≤ a (max m n)"
      by (rule levi) simp
    also have "... ≤ b (max m n)"
      by (rule neprazni)
    also have "... ≤ b n"
      by (rule desni) simp
    finally show ?thesis .
  qed

  let ?A = "range a"

  have ogranicen: "bdd_above ?A"
    by (rule bdd_aboveI[where M = "b 0"])
       (auto intro: svi_krajevi)

  have donja: "a n ≤ Sup ?A" for n
    by (rule cSup_upper) (auto intro: ogranicen)

  have gornja: "Sup ?A ≤ b n" for n
    by (rule cSup_least) (auto intro: svi_krajevi)

  show ?thesis
    using donja gornja by blast
qed


lemma l3_3_1:
  fixes J::"nat ⇒ real set"
  assumes h: "umetnuti_odsecci2 J"
  shows "(⋂n. J n) ≠ {}"
proof -
  have postoje_krajevi:
    "∀n. ∃u v. u ≤ v ∧ J n = odsecak u v"
    using h
    unfolding umetnuti_odsecci2_def
    by blast

  obtain a :: "nat ⇒ real" where izbor_a:
    "∀n. ∃v. a n ≤ v ∧ J n = odsecak (a n) v"
    using choice[OF postoje_krajevi]
    by blast

  obtain b :: "nat ⇒ real" where krajevi:
    "∀n. a n ≤ b n ∧ J n = odsecak (a n) (b n)"
    using choice[OF izbor_a]
    by blast

  have ab: "a n ≤ b n" for n
    using krajevi by blast

  have Jn: "J n = odsecak (a n) (b n)" for n
    using krajevi by blast

  have korak: "J (Suc n) ⊆ J n" for n
    using h
    unfolding umetnuti_odsecci2_def
    by blast

  have umetnutost: "J n ⊆ J m" if "m ≤ n" for m n
    
    using lift_Suc_antimono_le[of J, OF korak, of m n] 
    using that by argo
  have levi_le_desni: "a m ≤ b n" for m n
  proof (cases "m ≤ n")
    case True

    have bn: "b n ∈ J n"
      using ab[of n]
      by (simp add: Jn odsecak_def)

    have "b n ∈ J m"
      using umetnutost[OF True] bn
      by blast

    then show ?thesis
      by (auto simp: Jn odsecak_def)
  next
    case False

    have nm: "n ≤ m"
      using False by arith

    have am: "a m ∈ J m"
      using ab[of m]
      by (simp add: Jn odsecak_def)

    have "a m ∈ J n"
      using umetnutost[OF nm] am
      by blast

    then show ?thesis
      by (auto simp: Jn odsecak_def)
  qed

  let ?A = "range a"  (* skracenica za skup svih vrednosti funkcije a, 
ovde su to svi elem niza *)

  have neprazan: "?A ≠ {}"
    by auto

  have ogranicen: "bdd_above ?A"
    by (rule bdd_aboveI[where M = "b 0"])
       (auto intro: levi_le_desni)

  have donja: "a n ≤ Sup ?A" for n
    by (rule cSup_upper[OF _ ogranicen]) auto

  have gornja: "Sup ?A ≤ b n" for n
    by (rule cSup_least[OF neprazan])
       (auto intro: levi_le_desni)

  have pripada: "Sup ?A ∈ J n" for n
    using donja[of n] gornja[of n]
    by (simp add: Jn odsecak_def)

  have "Sup ?A ∈ (⋂n. J n)"
    using pripada by auto

  then show ?thesis
    by blast
qed

lemma pozitivan_sabirak:
fixes x y :: real
assumes zbir: "x + y > 0"
shows "x > 0 ∨ y > 0"
proof (rule ccontr)
assume suprotno: "¬ (x > 0 ∨ y > 0)"
have x_nepoz: "x ≤ 0"
using suprotno by auto
have y_nepoz: "y ≤ 0"
using suprotno by auto
have zbir_nepoz: "x + y ≤ 0"
using x_nepoz y_nepoz by arith
show False
using zbir zbir_nepoz by arith
qed

end

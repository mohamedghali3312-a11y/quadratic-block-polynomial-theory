/-!
  QuadraticBlockDivision.lean — Division Euclidienne par Blocs Quadratiques & Récurrence de Lucas
  - Formalisation autonome en Lean 4 Pur (zéro Mathlib, zéro sorryAx)
  - Identité exacte de division P(x) = Q(x)*(x^2 + S*x + P) + (r0 + r1*x)
  - Évaluation quotientée P(r) = r0 + r1*r aux racines du bloc quadratique
  - Unicité du reste euclidien sur deux racines distinctes
  - Auteur : Mohamed Ghali (ORCID : 0009-0006-3364-5341)
-/

namespace QuadraticBlockDivision

def divModQuadDescAux : List Int → Int → Int → List Int → Int → Int → List Int × (Int × Int)
  | [], _, _, qAcc, r1, r0 => (qAcc.reverse, (r1, r0))
  | c :: cs, S, P, qAcc, r1, r0 =>
    divModQuadDescAux cs S P (r1 :: qAcc) (r0 - S * r1) (c - P * r1)

def divModQuadDesc (coeffsDesc : List Int) (S P : Int) : List Int × (Int × Int) :=
  divModQuadDescAux coeffsDesc S P [] 0 0

def evalDescAux : List Int → Int → Int → Int
  | [], _, acc => acc
  | c :: cs, x, acc => evalDescAux cs x (acc * x + c)

def evalDesc (coeffsDesc : List Int) (x : Int) : Int :=
  evalDescAux coeffsDesc x 0

theorem divModQuadDescAux_invariant
    (cs : List Int) (S P x : Int) (qAcc : List Int) (r1 r0 : Int) :
    let res := divModQuadDescAux cs S P qAcc r1 r0
    evalDescAux cs x (evalDescAux qAcc.reverse x 0 * (x * x + S * x + P) + (r1 * x + r0)) =
    evalDescAux res.1 x 0 * (x * x + S * x + P) + (res.2.1 * x + res.2.2) := by
  induction cs generalizing qAcc r1 r0 with
  | nil =>
    simp only [divModQuadDescAux, evalDescAux]
  | cons c cs ih =>
    dsimp only [divModQuadDescAux, evalDescAux]
    have h_horner : evalDescAux (r1 :: qAcc).reverse x 0 =
        evalDescAux qAcc.reverse x 0 * x + r1 := by
      rw [List.reverse_cons]
      have h_app : ∀ (l : List Int) (acc : Int),
          evalDescAux (l ++ [r1]) x acc = evalDescAux l x acc * x + r1 := by
        intro l
        induction l with
        | nil => simp only [List.nil_append, evalDescAux]
        | cons u us ihl =>
          intro acc
          simp only [List.cons_append, evalDescAux]
          exact ihl (acc * x + u)
      exact h_app qAcc.reverse 0
    have h_step_alg :
        (evalDescAux qAcc.reverse x 0 * (x * x + S * x + P) + (r1 * x + r0)) * x + c =
        (evalDescAux qAcc.reverse x 0 * x + r1) * (x * x + S * x + P) +
        ((r0 - S * r1) * x + (c - P * r1)) := by
      simp only [Int.add_mul, Int.mul_add, Int.sub_mul]
      have h_re1 : (r1 * x) * x = r1 * (x * x) := by ac_rfl
      have h_re2 : (S * r1) * x = r1 * (S * x) := by ac_rfl
      have h_re3 : P * r1 = r1 * P := Int.mul_comm P r1
      rw [h_re1, h_re2, h_re3]
      omega
    rw [h_step_alg, ← h_horner]
    exact ih (r1 :: qAcc) (r0 - S * r1) (c - P * r1)

/-- THÉORÈME 1 (Identité Exacte de Division Euclidienne par Bloc Quadratique) :
    Pour tout polynôme P(x) et tout bloc B(x) = x^2 + S*x + P,
    P(x) = Q(x) * (x^2 + S*x + P) + (r1 * x + r0) -/
theorem theorem1_quadratic_euclidean_division (coeffsDesc : List Int) (S P x : Int) :
    let res := divModQuadDesc coeffsDesc S P
    evalDesc coeffsDesc x =
    evalDesc res.1 x * (x * x + S * x + P) + (res.2.1 * x + res.2.2) := by
  dsimp only [divModQuadDesc, evalDesc]
  have h0 := divModQuadDescAux_invariant coeffsDesc S P x [] 0 0
  simp only [List.reverse_nil, evalDescAux, Int.zero_mul, Int.zero_add] at h0
  exact h0

/-- THÉORÈME 2 (Théorème du Reste Quadratique aux Racines du Bloc) :
    Si r est une racine de x^2 + S*x + P = 0, alors P(r) = r1 * r + r0 -/
theorem theorem2_quadratic_remainder_at_root
    (coeffsDesc : List Int) (S P r : Int)
    (hr : r * r + S * r + P = 0) :
    let rem := (divModQuadDesc coeffsDesc S P).2
    evalDesc coeffsDesc r = rem.1 * r + rem.2 := by
  have h_div := theorem1_quadratic_euclidean_division coeffsDesc S P r
  dsimp only at h_div ⊢
  rw [hr, Int.mul_zero, Int.zero_add] at h_div
  exact h_div

/-- THÉORÈME 3 (Unicité du Reste Linéaire sur Deux Racines Distinctes) :
    Si r1*ra + r0 = r1'*ra + r0' et r1*rb + r0 = r1'*rb + r0' avec ra ≠ rb,
    alors r1 = r1' et r0 = r0' -/
theorem theorem3_quadratic_remainder_uniqueness
    (r1 r0 r1' r0' ra rb : Int)
    (h_ne : ra ≠ rb)
    (ha : r1 * ra + r0 = r1' * ra + r0')
    (hb : r1 * rb + r0 = r1' * rb + r0') :
    r1 = r1' ∧ r0 = r0' := by
  have h_sub : (r1 - r1') * (ra - rb) = 0 := by
    have h_exp : (r1 - r1') * (ra - rb) = (r1 * ra + r0) - (r1' * ra + r0') -
                 ((r1 * rb + r0) - (r1' * rb + r0')) := by
      simp only [Int.sub_mul, Int.mul_sub]
      omega
    rw [ha, hb] at h_exp
    simp only [Int.sub_self] at h_exp
    exact h_exp
  have h_diff_ne : ra - rb ≠ 0 := by omega
  have hr1_eq : r1 - r1' = 0 := (Int.mul_eq_zero.mp h_sub).resolve_right h_diff_ne
  have hr1 : r1 = r1' := by omega
  rw [hr1] at ha
  have hr0 : r0 = r0' := by omega
  exact ⟨hr1, hr0⟩

#print axioms theorem1_quadratic_euclidean_division
#print axioms theorem2_quadratic_remainder_at_root
#print axioms theorem3_quadratic_remainder_uniqueness

end QuadraticBlockDivision

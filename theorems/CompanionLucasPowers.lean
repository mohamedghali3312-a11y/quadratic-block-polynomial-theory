/-!
  CompanionLucasPowers.lean — Puissances x^k mod (x^2 + S*x + P) & Identité de Cassini–Lucas
  - Formalisation autonome en Lean 4 Pur (zéro Mathlib, zéro sorryAx)
  - Théorème 1 : Réduction exacte x^k = Q_k(x)*(x^2 + S*x + P) + (u_k*x + v_k)
  - Théorème 2 : Évaluation aux racines r^k = u_k*r + v_k
  - Théorème 3 : Récurrence linéaire d'ordre 2 (u_{k+2} + S*u_{k+1} + P*u_k = 0)
  - Théorème 4 : Identité généralisée de Cassini–Simson (u_k*v_{k+1} - u_{k+1}*v_k = P^k)
  - Auteur     : Mohamed Ghali (ORCID : 0009-0006-3364-5341)
-/

namespace CompanionLucasPowers

def intPow (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => intPow x k * x

def companionState (S P : Int) : Nat → Int × Int
  | 0 => (0, 1)
  | k + 1 =>
    let (u, v) := companionState S P k
    (v - S * u, -P * u)

def uSeq (S P : Int) (k : Nat) : Int :=
  (companionState S P k).1

def vSeq (S P : Int) (k : Nat) : Int :=
  (companionState S P k).2

def companionQuotientEval (S P x : Int) : Nat → Int
  | 0 => 0
  | k + 1 => companionQuotientEval S P x k * x + uSeq S P k

/-- THÉORÈME 1 (Réduction Euclidienne Exacte de x^k modulo x^2 + S*x + P) :
    Pour tout k >= 0, x^k = Q_k(x) * (x^2 + S*x + P) + (u_k * x + v_k) -/
theorem theorem1_x_pow_mod_quad_exact (S P x : Int) (k : Nat) :
    intPow x k =
    companionQuotientEval S P x k * (x * x + S * x + P) + (uSeq S P k * x + vSeq S P k) := by
  induction k with
  | zero =>
    simp only [intPow, companionQuotientEval, uSeq, vSeq, companionState,
               Int.zero_mul, Int.zero_add]
  | succ m ih =>
    dsimp only [intPow, companionQuotientEval, uSeq, vSeq, companionState]
    rw [ih]
    have h_alg :
        (companionQuotientEval S P x m * (x * x + S * x + P) +
          ((companionState S P m).1 * x + (companionState S P m).2)) * x =
        (companionQuotientEval S P x m * x + (companionState S P m).1) * (x * x + S * x + P) +
        (((companionState S P m).2 - S * (companionState S P m).1) * x +
          (-P * (companionState S P m).1)) := by
      simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.neg_mul]
      have h1 : ((companionState S P m).1 * x) * x = (companionState S P m).1 * (x * x) := by
        ac_rfl
      have h2 : (S * (companionState S P m).1) * x = (companionState S P m).1 * (S * x) := by
        ac_rfl
      have h3 : P * (companionState S P m).1 = (companionState S P m).1 * P :=
        Int.mul_comm P (companionState S P m).1
      rw [h1, h2, h3]
      omega
    exact h_alg

/-- THÉORÈME 2 (Évaluation Directe des Puissances aux Racines du Bloc) :
    Si r^2 + S*r + P = 0, alors r^k = u_k * r + v_k pour tout k >= 0 -/
theorem theorem2_x_pow_at_root (S P r : Int) (hr : r * r + S * r + P = 0) (k : Nat) :
    intPow r k = uSeq S P k * r + vSeq S P k := by
  have h := theorem1_x_pow_mod_quad_exact S P r k
  rw [hr, Int.mul_zero, Int.zero_add] at h
  exact h

/-- THÉORÈME 3 (Équation Caractéristique Linéaire d'Ordre 2 des Suites de Lucas) :
    u_{k+2} + S * u_{k+1} + P * u_k = 0 et v_{k+2} + S * v_{k+1} + P * v_k = 0 -/
theorem theorem3_lucas_second_order_recurrence (S P : Int) (k : Nat) :
    (uSeq S P (k + 2) + S * uSeq S P (k + 1) + P * uSeq S P k = 0) ∧
    (vSeq S P (k + 2) + S * vSeq S P (k + 1) + P * vSeq S P k = 0) := by
  constructor
  · have hu2 : uSeq S P (k + 2) = vSeq S P (k + 1) - S * uSeq S P (k + 1) := rfl
    have hv1 : vSeq S P (k + 1) = -P * uSeq S P k := rfl
    rw [hu2, hv1]
    simp only [Int.neg_mul]
    omega
  · have hv2 : vSeq S P (k + 2) = -P * uSeq S P (k + 1) := rfl
    have hv1 : vSeq S P (k + 1) = -P * uSeq S P k := rfl
    have hu1 : uSeq S P (k + 1) = vSeq S P k - S * uSeq S P k := rfl
    rw [hv2, hv1, hu1]
    simp only [Int.mul_sub, Int.neg_mul]
    have h_comm : P * (S * uSeq S P k) = S * (P * uSeq S P k) := by ac_rfl
    rw [h_comm]
    omega

/-- THÉORÈME 4 (Identité Généralisée de Cassini–Simson pour les Suites de Lucas) :
    u_k * v_{k+1} - u_{k+1} * v_k = P^k pour tout k >= 0 -/
theorem theorem4_generalized_cassini_identity (S P : Int) (k : Nat) :
    uSeq S P k * vSeq S P (k + 1) - uSeq S P (k + 1) * vSeq S P k = intPow P k := by
  induction k with
  | zero =>
    simp only [uSeq, vSeq, companionState, intPow, Int.mul_zero, Int.mul_one,
               Int.sub_zero, Int.zero_sub, Int.neg_zero]
  | succ m ih =>
    dsimp only [intPow]
    have hu2 : uSeq S P (m + 2) = vSeq S P (m + 1) - S * uSeq S P (m + 1) := rfl
    have hv2 : vSeq S P (m + 2) = -P * uSeq S P (m + 1) := rfl
    have hv1 : vSeq S P (m + 1) = -P * uSeq S P m := rfl
    have hu1 : uSeq S P (m + 1) = vSeq S P m - S * uSeq S P m := rfl
    rw [hu2, hv2]
    have h_step_det :
        uSeq S P (m + 1) * (-P * uSeq S P (m + 1)) -
        (vSeq S P (m + 1) - S * uSeq S P (m + 1)) * vSeq S P (m + 1) =
        (uSeq S P m * vSeq S P (m + 1) - uSeq S P (m + 1) * vSeq S P m) * P := by
      rw [hu1, hv1]
      simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have h_u2 : (vSeq S P m - S * uSeq S P m) * (P * (vSeq S P m - S * uSeq S P m)) =
                  P * ((vSeq S P m - S * uSeq S P m) * (vSeq S P m - S * uSeq S P m)) := by
        ac_rfl
      have h_sq : (vSeq S P m - S * uSeq S P m) * (vSeq S P m - S * uSeq S P m) =
                  vSeq S P m * vSeq S P m - 2 * (S * (uSeq S P m * vSeq S P m)) +
                  (S * uSeq S P m) * (S * uSeq S P m) := by
        simp only [Int.sub_mul, Int.mul_sub]
        have hc : vSeq S P m * (S * uSeq S P m) = S * (uSeq S P m * vSeq S P m) := by ac_rfl
        have hc2 : (S * uSeq S P m) * vSeq S P m = S * (uSeq S P m * vSeq S P m) := by ac_rfl
        rw [hc, hc2]
        omega
      rw [h_u2, h_sq]
      simp only [Int.mul_add, Int.mul_sub]
      have ha1 : P * (vSeq S P m * vSeq S P m) = (vSeq S P m * vSeq S P m) * P :=
        Int.mul_comm P _
      have ha2 : P * (2 * (S * (uSeq S P m * vSeq S P m))) =
                 2 * ((S * (uSeq S P m * vSeq S P m)) * P) := by ac_rfl
      have ha3 : P * ((S * uSeq S P m) * (S * uSeq S P m)) =
                 (S * (vSeq S P m - S * uSeq S P m)) * (P * uSeq S P m) +
                 (S * (uSeq S P m * vSeq S P m)) * P := by
        simp only [Int.mul_sub]
        have ht1 : (S * (vSeq S P m - S * uSeq S P m)) * (P * uSeq S P m) =
                   (S * (uSeq S P m * vSeq S P m)) * P -
                   P * ((S * uSeq S P m) * (S * uSeq S P m)) := by
          simp only [Int.mul_sub, Int.sub_mul]
          have hb1 : (S * vSeq S P m) * (P * uSeq S P m) =
                     (S * (uSeq S P m * vSeq S P m)) * P := by ac_rfl
          have hb2 : (S * (S * uSeq S P m)) * (P * uSeq S P m) =
                     P * ((S * uSeq S P m) * (S * uSeq S P m)) := by ac_rfl
          rw [hb1, hb2]
        omega
      have ha4 : (uSeq S P m * (-P * uSeq S P m) -
                  (vSeq S P m - S * uSeq S P m) * vSeq S P m) * P =
                 (-(uSeq S P m * (P * uSeq S P m)) * P -
                  ((vSeq S P m * vSeq S P m) * P - (S * (uSeq S P m * vSeq S P m)) * P)) := by
        simp only [Int.neg_mul, Int.sub_mul, Int.mul_neg]
        have hc3 : (S * uSeq S P m) * vSeq S P m = S * (uSeq S P m * vSeq S P m) := by ac_rfl
        rw [hc3]
        omega
      have ha5 : P * (uSeq S P m * uSeq S P m) = uSeq S P m * (P * uSeq S P m) := by ac_rfl
      rw [ha1, ha2, ha3, ha4, ha5]
      omega
    rw [h_step_det, ih]

#print axioms theorem1_x_pow_mod_quad_exact
#print axioms theorem2_x_pow_at_root
#print axioms theorem3_lucas_second_order_recurrence
#print axioms theorem4_generalized_cassini_identity

end CompanionLucasPowers

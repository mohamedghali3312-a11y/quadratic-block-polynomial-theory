/-!
  QuadraticBlockTheory.lean — Théorie Pure de la Factorisation Polynomiale par Blocs Quadratiques
  - Formalisation autonome en Lean 4 Pur (zéro Mathlib, zéro sorryAx)
  - Partie I   : Algèbre des blocs quadratiques en degré n = 2m et relations de Viète par blocs
  - Partie II  : Théorème du résultant de Sylvester–Jacobien et singularité des racines multiples
  - Partie III : Coercivité spectrale uniforme sur le cône symétrique semi-défini positif
  - Auteur     : Mohamed Ghali (ORCID : 0009-0006-3364-5341)
-/

namespace QuadraticBlockTheory

-- ============================================================================
-- PARTIE I : ALGÈBRE DES POLYNÔMES ET BLOCS QUADRATIQUES EN DEGRÉ n = 2m
-- ============================================================================

abbrev Poly := List Int

def polyEval : Poly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * polyEval cs x

def polyAdd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

def polyScale (k : Int) : Poly → Poly
  | [] => []
  | a :: as => (k * a) :: polyScale k as

def polyMul : Poly → Poly → Poly
  | [], _ => []
  | a :: as, q => polyAdd (polyScale a q) (0 :: polyMul as q)

def quadBlock (S P : Int) : Poly :=
  [P, S, 1]

def blockProd : List (Int × Int) → Poly
  | [] => [1]
  | (S, P) :: rest => polyMul (quadBlock S P) (blockProd rest)

def prodConsts : List (Int × Int) → Int
  | [] => 1
  | (_, P) :: rest => P * prodConsts rest

theorem polyEval_polyAdd (p q : Poly) (x : Int) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil =>
    cases q <;> simp only [polyAdd, polyEval, Int.zero_add]
  | cons a as ih =>
    cases q with
    | nil => simp only [polyAdd, polyEval, Int.add_zero]
    | cons b bs =>
      simp only [polyAdd, polyEval, ih, Int.mul_add]
      omega

theorem polyEval_polyScale (k : Int) (p : Poly) (x : Int) :
    polyEval (polyScale k p) x = k * polyEval p x := by
  induction p with
  | nil => simp only [polyScale, polyEval, Int.mul_zero]
  | cons a as ih =>
    simp only [polyScale, polyEval, ih, Int.mul_add]
    have h_assoc : x * (k * polyEval as x) = k * (x * polyEval as x) := by ac_rfl
    rw [h_assoc]

theorem polyEval_polyMul (p q : Poly) (x : Int) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil => simp only [polyMul, polyEval, Int.zero_mul]
  | cons a as ih =>
    simp only [polyMul, polyEval, polyEval_polyAdd, polyEval_polyScale, ih,
               Int.zero_add, Int.add_mul]
    have h_assoc : x * (polyEval as x * polyEval q x) = (x * polyEval as x) * polyEval q x := by
      ac_rfl
    rw [h_assoc]

def constCoeff : Poly → Int
  | [] => 0
  | a :: _ => a

theorem constCoeff_polyAdd (p q : Poly) :
    constCoeff (polyAdd p q) = constCoeff p + constCoeff q := by
  cases p with
  | nil => cases q <;> simp only [polyAdd, constCoeff, Int.zero_add]
  | cons a as =>
    cases q with
    | nil => simp only [polyAdd, constCoeff, Int.add_zero]
    | cons b bs => simp only [polyAdd, constCoeff]

theorem constCoeff_polyScale (k : Int) (p : Poly) :
    constCoeff (polyScale k p) = k * constCoeff p := by
  cases p with
  | nil => simp only [polyScale, constCoeff, Int.mul_zero]
  | cons a as => simp only [polyScale, constCoeff]

theorem constCoeff_polyMul (p q : Poly) :
    constCoeff (polyMul p q) = constCoeff p * constCoeff q := by
  cases p with
  | nil => simp only [polyMul, constCoeff, Int.zero_mul]
  | cons a as =>
    dsimp only [polyMul]
    rw [constCoeff_polyAdd, constCoeff_polyScale]
    simp only [constCoeff, Int.add_zero]

/-- Théorème I.1 : Relation de Viète d'ordre 0 en degré quelconque n = 2m -/
theorem blockProd_const_term_eq_prod (blocks : List (Int × Int)) :
    constCoeff (blockProd blocks) = prodConsts blocks := by
  induction blocks with
  | nil => simp only [blockProd, constCoeff, prodConsts]
  | cons hd rest ih =>
    rcases hd with ⟨S, P⟩
    dsimp only [blockProd, prodConsts]
    rw [constCoeff_polyMul, ← ih]
    simp only [quadBlock, constCoeff]

/-- Théorème I.2 : Équivalence complète en degré n = 4 (Produit de 2 blocs ↔ 4 équations de Viète) -/
theorem degree4_viete_system_equivalence (S1 P1 S2 P2 a3 a2 a1 a0 : Int) :
    blockProd [(S1, P1), (S2, P2)] = [a0, a1, a2, a3, 1] ↔
    (P1 * P2 = a0 ∧
     S1 * P2 + S2 * P1 = a1 ∧
     P1 + P2 + S1 * S2 = a2 ∧
     S1 + S2 = a3) := by
  have h_prod : blockProd [(S1, P1), (S2, P2)] =
      [P1 * P2, S1 * P2 + P1 * S2, P1 + S1 * S2 + P2, S1 + S2, 1] := by
    dsimp only [blockProd, quadBlock, polyMul, polyAdd, polyScale]
    simp only [Int.mul_one, Int.mul_zero, Int.add_zero, Int.zero_add]
  rw [h_prod]
  constructor
  · intro h
    injection h with h0 h_rest1
    injection h_rest1 with h1 h_rest2
    injection h_rest2 with h2 h_rest3
    injection h_rest3 with h3 _
    have h1' : S1 * P2 + S2 * P1 = a1 := by
      have hc : P1 * S2 = S2 * P1 := Int.mul_comm P1 S2
      omega
    have h2' : P1 + P2 + S1 * S2 = a2 := by omega
    exact ⟨h0, h1', h2', h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    have h1' : S1 * P2 + P1 * S2 = a1 := by
      have hc : P1 * S2 = S2 * P1 := Int.mul_comm P1 S2
      omega
    have h2' : P1 + S1 * S2 + P2 = a2 := by omega
    rw [h0, h1', h2', h3]

theorem quadBlock_eval_root (S P r : Int) (hr : r * r + S * r + P = 0) :
    polyEval (quadBlock S P) r = 0 := by
  dsimp only [quadBlock, polyEval]
  have h_re : P + r * (S + r * (1 + r * 0)) = r * r + S * r + P := by
    simp only [Int.mul_zero, Int.add_zero, Int.mul_one, Int.mul_add]
    ac_rfl
  rw [h_re, hr]

/-- Théorème I.3 : Annulation globale de prod_{j=1}^m B_j(x) aux racines de chaque bloc -/
theorem blockProd_eval_zero_of_mem_root (blocks : List (Int × Int)) (S P r : Int)
    (h_mem : (S, P) ∈ blocks) (hr : r * r + S * r + P = 0) :
    polyEval (blockProd blocks) r = 0 := by
  induction blocks with
  | nil => cases h_mem
  | cons hd rest ih =>
    rcases hd with ⟨S0, P0⟩
    dsimp only [blockProd]
    rw [polyEval_polyMul]
    rcases List.mem_cons.mp h_mem with h_eq | h_tail
    · injection h_eq with hS hP
      rw [hS, hP, quadBlock_eval_root S P r hr, Int.zero_mul]
    · rw [ih h_tail, Int.mul_zero]

-- ============================================================================
-- PARTIE II : THÉORÈME DU RÉSULTANT DE SYLVESTER–JACOBIEN
-- ============================================================================

def quadLinearResultant (S P c1 c0 : Int) : Int :=
  c0 * c0 - S * c0 * c1 + P * c1 * c1

def quadBlockJacobianDet (S P c1 c0 : Int) : Int :=
  (c0 - S * c1) * c0 - c1 * (-P * c1)

/-- Théorème II.1 : Égalité exacte det(J) = Res(x^2 + S*x + P, c1*x + c0) -/
theorem jacobian_det_equals_resultant (S P c1 c0 : Int) :
    quadBlockJacobianDet S P c1 c0 = quadLinearResultant S P c1 c0 := by
  dsimp only [quadBlockJacobianDet, quadLinearResultant]
  have h1 : (c0 - S * c1) * c0 = c0 * c0 - S * c0 * c1 := by
    rw [Int.sub_mul]
    have hm : (S * c1) * c0 = S * c0 * c1 := by ac_rfl
    rw [hm]
  have h2 : c1 * (-P * c1) = -(P * c1 * c1) := by
    have hm : c1 * (-P * c1) = -(c1 * (P * c1)) := by
      rw [Int.neg_mul, Int.mul_neg]
    rw [hm]
    have ha : c1 * (P * c1) = P * c1 * c1 := by ac_rfl
    rw [ha]
  rw [h1, h2, Int.sub_neg_eq_add]

/-- Théorème II.2 : Toute racine commune à B(x) et Q(x) annule le déterminant jacobien -/
theorem common_root_implies_singular_jacobian
    (S P c1 c0 r : Int)
    (hB : r * r + S * r + P = 0)
    (hQ : c1 * r + c0 = 0) :
    quadBlockJacobianDet S P c1 c0 = 0 := by
  rw [jacobian_det_equals_resultant]
  dsimp only [quadLinearResultant]
  have hc0 : c0 = -(c1 * r) := by omega
  rw [hc0]
  have h_id : (-(c1 * r)) * (-(c1 * r)) - S * (-(c1 * r)) * c1 + P * c1 * c1 =
              (r * r + S * r + P) * (c1 * c1) := by
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.sub_neg_eq_add, Int.add_mul]
    ac_rfl
  rw [h_id, hB, Int.zero_mul]

-- ============================================================================
-- PARTIE III : COERCIVITÉ SPECTRALE UNIFORME SUR LE CÔNE SEMI-DÉFINI POSITIF
-- ============================================================================

structure SymMat2 where
  a : Int
  b : Int
  c : Int
deriving DecidableEq

def SymMat2.det (M : SymMat2) : Int :=
  M.a * M.c - M.b * M.b

def IsPSD (M : SymMat2) : Prop :=
  0 ≤ M.a ∧ 0 ≤ M.c ∧ 0 ≤ M.det

/-- Théorème III.1 : Borne spectrale uniforme det(M + mu*I_2) >= mu^2 > 0 -/
theorem spectral_shift_uniform_coercivity (M : SymMat2) (hM : IsPSD M) (mu : Int) (hmu : 0 < mu) :
    let M_reg : SymMat2 := ⟨M.a + mu, M.b, M.c + mu⟩
    mu * mu ≤ M_reg.det ∧ 0 < M_reg.det := by
  rcases hM with ⟨ha, hc, hd⟩
  dsimp only [SymMat2.det] at hd ⊢
  have h_expand : (M.a + mu) * (M.c + mu) - M.b * M.b =
      (M.a * M.c - M.b * M.b) + mu * (M.a + M.c) + mu * mu := by
    simp only [Int.add_mul, Int.mul_add]
    omega
  have h_trace_nn : 0 ≤ mu * (M.a + M.c) := Int.mul_nonneg (by omega) (by omega)
  have h_mu_sq_pos : 0 < mu * mu := Int.mul_pos hmu hmu
  omega

#print axioms blockProd_const_term_eq_prod
#print axioms degree4_viete_system_equivalence
#print axioms blockProd_eval_zero_of_mem_root
#print axioms jacobian_det_equals_resultant
#print axioms common_root_implies_singular_jacobian
#print axioms spectral_shift_uniform_coercivity

end QuadraticBlockTheory

# Quadratic Block Polynomial Theory — Formalisation en Lean 4 Pur (v1.0.0)

[![Lean 4 CI](https://github.com)](https://github.com)
[![ORCID](https://shields.io)](https://orcid.org)
[![Lean 4](https://shields.io)](https://lean-lang.org)

Théorie algébrique et spectrale pure de la **factorisation polynomiale par blocs quadratiques** $B_j(x) = x^2 + S_j x + P_j$, formalisée et vérifiée mécaniquement dans le noyau autonome de **Lean 4** (zéro dépendance externe, zéro `Mathlib`, zéro `sorryAx`).

---

## Théorèmes Formels Certifiés (Build CI #8 ✅)

| Module Lean 4 | Théorèmes principaux | Résultats établis | Axiomes utilisés |
| :--- | :--- | :--- | :--- |
| `theorems/QuadraticBlockTheory.lean` | `blockProd_const_term_eq_prod`<br>`degree4_viete_system_equivalence`<br>`jacobian_det_equals_resultant`<br>`spectral_shift_uniform_coercivity` | • Relations de Viète par blocs en degré $n = 2m$ ($a_0 = \prod P_j$)<br>• Équivalence logique complète en degré 4<br>• Identité du résultant de Sylvester–Jacobien ($\det J = \operatorname{Res}(B_j, Q_j)$)<br>• Coercivité spectrale uniforme $\det(M + \mu I_2) \ge \mu^2 > 0$ | `[propext, Quot.sound]` |
| `theorems/QuadraticBlockDivision.lean` | `theorem1_quadratic_euclidean_division`<br>`theorem2_quadratic_remainder_at_root`<br>`theorem3_quadratic_remainder_uniqueness` | • Identité exacte de division euclidienne $P(x) = Q(x)B(x) + r_1 x + r_0$<br>• Évaluation quotientée aux racines $P(r) = r_1 r + r_0$<br>• Unicité du reste linéaire sur deux racines distinctes | `[propext, Quot.sound]` |
| `theorems/CompanionLucasPowers.lean` | `theorem1_x_pow_mod_quad_exact`<br>`theorem3_lucas_second_order_recurrence`<br>`theorem4_generalized_cassini_identity` | • Réduction exacte des puissances $x^k = Q_k(x)B(x) + u_k x + v_k$<br>• Équation caractéristique d'ordre 2 des suites de Lucas<br>• Identité généralisée de Cassini–Simson ($u_k v_{k+1} - u_{k+1} v_k = P^k$) | `[propext, Quot.sound]` |

---

## Reproductibilité & Audit CI

Tous les modules sont compilés et audités automatiquement via `#print axioms` à chaque commit :

```bash
lean theorems/QuadraticBlockTheory.lean
lean theorems/QuadraticBlockDivision.lean
lean theorems/CompanionLucasPowers.lean
```

## Références & Auteur

- **Auteur :** Mohamed Ghali ([ORCID : 0009-0006-3364-5341](https://orcid.org))
- **Manuscrit associé :** *Factorisation Réelle & Complexe des Polynômes par Blocs Quadratiques Régularisés (MBC-Annealing v5)* — [`hal-05860758`](https://hal.science)
- **Dépôts liés :** `VULCAIN-Architecture` (`10.5281/zenodo.24345657`), `algebraic-quotient-duality` (`10.5281/zenodo.24525843`)

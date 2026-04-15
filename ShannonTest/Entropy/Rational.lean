import Shannon.Entropy.Rational
import Shannon.Entropy.Converse

/-!
# Shannon Entropy: Rational Tests

Exercises for rational-count refinements and the worked `(1/2, 1/3, 1/6)`
decomposition.
-/

open Shannon

example :
    relabelProb (Fintype.equivFinOfCardEq (by native_decide))
      (composeProb (uniformPNat 2) (fun _ : Fin 2 => uniformPNat 1))
      = uniformPNat 2 := by
  simpa using
    relabel_compose_rational_eq_uniform
      (p := uniformPNat 2)
      (n := fun _ : Fin 2 => 1)
      (hpos := fun _ : Fin 2 => show 0 < (1 : ℕ) from by decide)
      (N := 2)
      (hN := by decide)
      (hp := by intro a; norm_num [uniformPNat])
      (e := Fintype.equivFinOfCardEq (by native_decide))

example (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) {α : Type} [Fintype α]
    (p : ProbDist α) (n : α → ℕ) (hpos : ∀ a, 0 < n a)
    (N : ℕ) (hN : 0 < N) (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    Apos H ⟨N, hN⟩ = H p + ∑ a, p a * Apos H ⟨n a, hpos a⟩ :=
  grouping_on_rational_counts H hH p n hpos N hN hsum hp

example :
    entropyNat (uniformPNat 3)
      = -K entropyNat * ∑ a, (uniformPNat 3) a * Real.log ((uniformPNat 3) a) := by
  simpa using
    entropyNat_of_rational_counts
      entropyNat
      entropyNat_shannonAxioms
      (uniformPNat 3)
      (fun _ : Fin 3 => 1)
      (fun _ : Fin 3 => show 0 < (1 : ℕ) from by decide)
      3
      (by decide)
      (by decide)
      (by intro a; norm_num [uniformPNat])

example :
    workedCompose ⟨true, (0 : Fin 1)⟩ = (1 : ℝ) / 2 ∧
      workedCompose ⟨false, (0 : Fin 2)⟩ = (1 : ℝ) / 3 ∧
      workedCompose ⟨false, (1 : Fin 2)⟩ = (1 : ℝ) / 6 :=
  workedCompose_masses

example :
    entropyNat workedCompose = entropyNat workedP + (1 / 2 : ℝ) * entropyNat (workedQ false) :=
  worked_grouping_identity entropyNat entropyNat_shannonAxioms

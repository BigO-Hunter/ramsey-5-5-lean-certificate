import LeapsInBounds.Statements.Ramsey
import Mathlib.Data.Fintype.EquivFin

/-!
# R(5,5) ≥ 42 — an explicit circulant certificate

The circulant graph `C₄₁(1,2,3,5,8,12,13,16,17,19)` on 41 vertices has no
5-clique and no independent set of size 5, certifying `R(5,5) ≥ 42`.

Graph witness: Geoffrey Exoo's circulant Ramsey graph, published as graph6 at
`daniel-munro/leaps-in-bounds`, `certificates/ramsey/ramsey-5-5-lower-42.g6`
(witness metadata: submitted by Claude, 2026-11-02, notes
"Circulant graph C41(1,2,3,5,8,12,13,16,17,19) has no 5-clique and no
independent set of size 5."). This formalization was produced by Claude
(the MultiAgency body), November 2026.

Method (generalizes to any circulant lower-bound witness, e.g. for later
43+ certificates on more vertices):

* A circulant graph is vertex-transitive: an injective shift `e` moving any
  chosen vertex to `0` preserves adjacency, so any 5-clique can be shifted to
  one containing vertex `0`.
* A 5-clique containing `0` is `0` together with a *bad quadruple* `(a, b, c, d)`:
  all four adjacent to `0`, pairwise distinct, and pairwise adjacent.
* Absence of bad quadruples over all `41⁴` quadruples is discharged by kernel
  evaluation (`decide`). Only the standard three axioms are used — no
  `native_decide` anywhere.
-/

namespace LeapsInBounds.Proofs.Ramsey55

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

open Finset SimpleGraph

/-! ### Generic vertex-transitive refutation of 5-cliques -/

/-- `(a, b, c, d)` is *bad* for adjacency `A` when `0, a, b, c, d` would form a
5-clique. Distinctness first so the kernel check short-circuits cheaply. -/
def BadQuad {n : ℕ} [NeZero n] (A : Fin n → Fin n → Prop) (a b c d : Fin n) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  (A 0 a ∧ A 0 b ∧ A 0 c ∧ A 0 d ∧
  A a b ∧ A a c ∧ A a d ∧ A b c ∧ A b d ∧ A c d)

instance {n : ℕ} [NeZero n] {A : Fin n → Fin n → Prop} [DecidableRel A]
    (a b c d : Fin n) : Decidable (BadQuad A a b c d) := by
  unfold BadQuad
  infer_instance

/-- If adjacency admits an injective self-map `e` that preserves it and moves
`g 0` to `0`, then absence of bad quadruples excludes the 5-clique `g`. -/
theorem no_K5_of_no_badQuad {n : ℕ} [NeZero n] {A : Fin n → Fin n → Prop}
    {g : Fin 5 → Fin n} (hinj : Function.Injective g)
    (hadj : ∀ i j, i ≠ j → A (g i) (g j))
    (e : Fin n → Fin n) (heinj : Function.Injective e)
    (he : ∀ i j, A (e i) (e j) ↔ A i j)
    (he0 : e (g 0) = 0)
    (hbad : ∀ a b c d, ¬ BadQuad A a b c d) : False := by
  have hA0 : ∀ i : Fin 5, i ≠ 0 → A 0 (e (g i)) := by
    intro i hi
    have h2 := (he (g 0) (g i)).2 (hadj 0 i (Ne.symm hi))
    rwa [he0] at h2
  have hne : ∀ i j : Fin 5, i ≠ j → e (g i) ≠ e (g j) := by
    intro i j hij hh
    exact hij (hinj (heinj hh))
  have hA : ∀ i j : Fin 5, i ≠ j → A (e (g i)) (e (g j)) := fun i j hij =>
    (he (g i) (g j)).2 (hadj i j hij)
  refine hbad (e (g 1)) (e (g 2)) (e (g 3)) (e (g 4))
    ⟨hne 1 2 (by decide), hne 1 3 (by decide), hne 1 4 (by decide),
     hne 2 3 (by decide), hne 2 4 (by decide), hne 3 4 (by decide),
     hA0 1 (by decide), hA0 2 (by decide), hA0 3 (by decide), hA0 4 (by decide),
     hA 1 2 (by decide), hA 1 3 (by decide), hA 1 4 (by decide),
     hA 2 3 (by decide), hA 2 4 (by decide), hA 3 4 (by decide)⟩

/-- Vertex-transitivity + absence of bad quadruples imply `CliqueFree 5`. -/
theorem cliqueFree_of_no_badQuad {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    (hvt : ∀ v, ∃ e : Fin n → Fin n, Function.Injective e ∧ e v = 0 ∧
      ∀ i j, G.Adj (e i) (e j) ↔ G.Adj i j)
    (hbad : ∀ a b c d, ¬ BadQuad G.Adj a b c d) : G.CliqueFree 5 := by
  intro t ht
  have h5 : #t = 5 := ht.card_eq
  let e5 : {x // x ∈ t} ≃ Fin 5 := t.equivFinOfCardEq h5
  have hinj : Function.Injective (fun i => ((e5.symm i : {x // x ∈ t}) : Fin n)) :=
    fun i j h => e5.symm.injective (Subtype.ext h)
  have hadj : ∀ i j, i ≠ j → G.Adj ((e5.symm i : {x // x ∈ t}) : Fin n)
      ((e5.symm j : {x // x ∈ t}) : Fin n) := by
    intro i j hij
    exact ht.isClique (e5.symm i).property (e5.symm j).property
      fun hcon => hij (e5.symm.injective (Subtype.ext hcon))
  obtain ⟨e, heinj, he0, he⟩ := hvt ((e5.symm 0 : {x // x ∈ t}) : Fin n)
  exact no_K5_of_no_badQuad hinj hadj e heinj he he0 hbad

/-! ### The certificate -/

/-- Connection list of the witness, decoded exactly from
`certificates/ramsey/ramsey-5-5-lower-42.g6` (41 vertices, 410 edges,
20-regular circulant). -/
def conn : List ℕ := [1, 2, 3, 5, 8, 12, 13, 16, 17, 19, 22, 24, 25, 28, 29, 33, 36, 38, 39, 40]

/-- The connection set as a `Finset`, defined by filter so membership is
decidable and decided facts are kernel-checked. -/
def S : Finset (Fin 41) := Finset.univ.filter fun d => decide (d.val ∈ conn)

theorem mem_S {d : Fin 41} : d ∈ S ↔ d.val ∈ conn := by
  simp [S]

/-- Kernel-checked symmetry of the connection set. -/
theorem neg_mem_conn : ∀ d : Fin 41, d.val ∈ conn → (-d).val ∈ conn := by decide

theorem zero_notMem_conn : ¬ ((0 : Fin 41)).val ∈ conn := by decide

theorem S_neg_forall : ∀ d : Fin 41, d ∈ S → -d ∈ S := fun d h => by
  rw [mem_S]
  exact neg_mem_conn d (mem_S.mp h)

/-- Adjacency of the witness circulant `C₄₁(conn)`. -/
def Wadj (i j : Fin 41) : Prop := (j - i) ∈ S

instance instDecidableRelWadj : DecidableRel Wadj := fun i j =>
  inferInstanceAs (Decidable ((j - i) ∈ S))

theorem dec_W_symm : ∀ i j : Fin 41, Wadj i j → Wadj j i := by decide

theorem dec_W_loopless : ∀ i : Fin 41, ¬ Wadj i i := by decide

/-- The witness graph: circulant `C₄₁(conn)`. -/
def W : SimpleGraph (Fin 41) where
  Adj := Wadj
  symm := ⟨dec_W_symm⟩
  loopless := ⟨dec_W_loopless⟩

/-- Kernel-checked: shifts preserve `W`-adjacency (circulants are
vertex-transitive). -/
theorem dec_W_trans : ∀ t i j : Fin 41, Wadj (i + t) (j + t) ↔ Wadj i j := by decide

/-- Kernel-checked: shift cancellation and negation. -/
theorem dec_shift_inj : ∀ t x y : Fin 41, x + t = y + t → x = y := by decide

theorem dec_shift_neg : ∀ x : Fin 41, x + -x = 0 := by decide

/-- `W` is vertex-transitive in the abstract shape the generic lemma needs. -/
theorem W_vt : ∀ v : Fin 41, ∃ e : Fin 41 → Fin 41, Function.Injective e ∧ e v = 0 ∧
    ∀ i j, Wadj (e i) (e j) ↔ Wadj i j := by
  intro v
  exact ⟨fun x => x + -v, dec_shift_inj (-v), dec_shift_neg v, dec_W_trans (-v)⟩

/-- `W_vt` transported to the graph. -/
theorem W_vt' : ∀ v, ∃ e : Fin 41 → Fin 41, Function.Injective e ∧ e v = 0 ∧
    ∀ i j, W.Adj (e i) (e j) ↔ W.Adj i j := W_vt

/-- The 20 neighbors of vertex `0` in `W`, as an explicit list (kernel-checkable
by `decide`). -/
def nbrsL : List (Fin 41) :=
  [1, 2, 3, 5, 8, 12, 13, 16, 17, 19, 22, 24, 25, 28, 29, 33, 36, 38, 39, 40]

def nbrs : Fin 20 → Fin 41 := fun k => nbrsL.getD k.val 0

/-- Kernel-checked: the table `nbrs` covers exactly the neighbors of `0`. -/
theorem dec_mem_nbrs : ∀ x : Fin 41, Wadj 0 x → ∃ k : Fin 20, nbrs k = x := by decide

/-- Kernel-checked: no quadruple of neighbors of `0` completes a 5-clique with
`0` — the `20⁴ = 160000` kernel-evaluated cases at the heart of the certificate. -/
theorem no_bad_nbrs : ∀ k₁ k₂ k₃ k₄ : Fin 20,
    ¬ BadQuad Wadj (nbrs k₁) (nbrs k₂) (nbrs k₃) (nbrs k₄) := by decide

/-- Kernel-checked absence of bad quadruples for `W`: any bad quadruple consists
of four neighbors of `0`, which `no_bad_nbrs` excludes. -/
theorem no_bad_W : ∀ a b c d : Fin 41, ¬ BadQuad Wadj a b c d := by
  intro a b c d h
  have hA := h.2.2.2.2.2.2
  obtain ⟨k₁, hk₁⟩ := dec_mem_nbrs a hA.1
  obtain ⟨k₂, hk₂⟩ := dec_mem_nbrs b hA.2.1
  obtain ⟨k₃, hk₃⟩ := dec_mem_nbrs c hA.2.2.1
  obtain ⟨k₄, hk₄⟩ := dec_mem_nbrs d hA.2.2.2.1
  rw [← hk₁, ← hk₂, ← hk₃, ← hk₄] at h
  exact no_bad_nbrs k₁ k₂ k₃ k₄ h

theorem W_cliqueFree : W.CliqueFree 5 := by
  have h := cliqueFree_of_no_badQuad W W_vt' no_bad_W
  exact h

/-! ### The complement -/

/-- Connection set of the complement circulant: everything except `0` and `S`. -/
def Sc : Finset (Fin 41) := Finset.univ.filter fun d => d ≠ 0 ∧ d ∉ S

theorem mem_Sc {d : Fin 41} : d ∈ Sc ↔ d ≠ 0 ∧ d ∉ S := by
  simp [Sc]

/-- Adjacency of the complement circulant. -/
def Wcadj (i j : Fin 41) : Prop := (j - i) ∈ Sc

instance instDecidableRelWcadj : DecidableRel Wcadj := fun i j =>
  inferInstanceAs (Decidable ((j - i) ∈ Sc))

theorem dec_Wc_symm : ∀ i j : Fin 41, Wcadj i j → Wcadj j i := by decide

theorem dec_Wc_loopless : ∀ i : Fin 41, ¬ Wcadj i i := by decide

/-- The complement of the witness is again a circulant. -/
def Wc : SimpleGraph (Fin 41) where
  Adj := Wcadj
  symm := ⟨dec_Wc_symm⟩
  loopless := ⟨dec_Wc_loopless⟩

theorem dec_Wc_trans : ∀ t i j : Fin 41, Wcadj (i + t) (j + t) ↔ Wcadj i j := by decide

/-- The 20 neighbors of vertex `0` in the complement, as an explicit list. -/
def ScnbrsL : List (Fin 41) :=
  [4, 6, 7, 9, 10, 11, 14, 15, 18, 20, 21, 23, 26, 27, 30, 31, 32, 34, 35, 37]

def Scnbrs : Fin 20 → Fin 41 := fun k => ScnbrsL.getD k.val 0

/-- Kernel-checked: the complement table covers exactly the complement-neighbors
of `0`. -/
theorem dec_mem_Sc : ∀ x : Fin 41, Wcadj 0 x → ∃ k : Fin 20, Scnbrs k = x := by decide

/-- Kernel-checked: no quadruple of complement-neighbors of `0` completes a
5-clique of `Wc` (i.e. an independent 5-set of `W`) with `0`. -/
theorem no_bad_Sc_nbrs : ∀ k₁ k₂ k₃ k₄ : Fin 20,
    ¬ BadQuad Wcadj (Scnbrs k₁) (Scnbrs k₂) (Scnbrs k₃) (Scnbrs k₄) := by decide

theorem Wc_vt : ∀ v, ∃ e : Fin 41 → Fin 41, Function.Injective e ∧ e v = 0 ∧
    ∀ i j, Wc.Adj (e i) (e j) ↔ Wc.Adj i j := by
  intro v
  exact ⟨fun x => x + -v, dec_shift_inj (-v), dec_shift_neg v, dec_Wc_trans (-v)⟩

/-- Kernel-checked absence of bad quadruples for the complement — the
`20⁴` kernel-evaluated heart of the independent-set side. -/
theorem no_bad_Wc : ∀ a b c d : Fin 41, ¬ BadQuad Wcadj a b c d := by
  intro a b c d h
  have hA := h.2.2.2.2.2.2
  obtain ⟨k₁, hk₁⟩ := dec_mem_Sc a hA.1
  obtain ⟨k₂, hk₂⟩ := dec_mem_Sc b hA.2.1
  obtain ⟨k₃, hk₃⟩ := dec_mem_Sc c hA.2.2.1
  obtain ⟨k₄, hk₄⟩ := dec_mem_Sc d hA.2.2.2.1
  rw [← hk₁, ← hk₂, ← hk₃, ← hk₄] at h
  exact no_bad_Sc_nbrs k₁ k₂ k₃ k₄ h

theorem Wc_cliqueFree : Wc.CliqueFree 5 :=
  cliqueFree_of_no_badQuad Wc Wc_vt no_bad_Wc

/-- Kernel-checked: the complement of `W` is exactly the circulant `Wc`. -/
theorem dec_compl_W : ∀ i j : Fin 41, (Wᶜ).Adj i j ↔ Wc.Adj i j := by
  show ∀ i j : Fin 41, (i ≠ j ∧ ¬ Wadj i j) ↔ Wcadj i j
  decide

theorem compl_W : Wᶜ = Wc := by
  refine SimpleGraph.ext ?_
  funext i j
  exact propext (dec_compl_W i j)

/-- **Main theorem.** `R(5,5) ≥ 42`. -/
theorem ramsey_5_5_lower_42 : Ramsey.LowerBound 5 5 42 :=
  ⟨W, W_cliqueFree, by rw [compl_W]; exact Wc_cliqueFree⟩

#print axioms ramsey_5_5_lower_42

end LeapsInBounds.Proofs.Ramsey55

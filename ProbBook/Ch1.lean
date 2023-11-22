import Mathlib.Init.Set
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Tactic.DeriveFintype
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Basic

variable {Ω : Type u}

-- Definition 1.2
-- A huge thanks to Eric Wieser for his help on zulip :)
class DistFunc (Ω : Type u) where
  prob : Set Ω → ℝ
  hp (E : Set Ω) : prob E ≥ 0
  hu : prob (Set.univ) = 1

class DiscreteDistFunc (Ω : Type u) :=
  hc : Countable Ω
  -- m returns probability
  m : Ω → ℝ
  hp (ω : Ω) : m ω ≥ 0
  hu : (∑' ω, (m ω)) = 1

@[simp]
noncomputable
instance DiscreteDistFunc.toDistFunc [d : DiscreteDistFunc Ω] : DistFunc Ω := {
  prob := fun (E : Set Ω) => (∑' (ω : E), (d.m ω))
  hp := by
    intro E
    simp [d.hp]
    have hp1 (ω : ↑E) : 0 ≤  d.m (↑ω)  := by exact d.hp _
    exact tsum_nonneg hp1
  hu := by
    simp [d.hu]
}

noncomputable
instance : Coe (DiscreteDistFunc Ω) (DistFunc Ω) where
  coe x := x.toDistFunc

def P [d : DistFunc Ω] (E : Set Ω) : ℝ := d.prob E

-- toOuterMeasure and toPMF
open MeasureTheory
open MeasureTheory.OuterMeasure

noncomputable
def DiscreteDistFunc.toOuterMeasure (d : DiscreteDistFunc Ω) : OuterMeasure Ω :=
  OuterMeasure.sum fun x : Ω => Real.toNNReal (d.m x) • dirac x

lemma Summable.of_tsum_ne_zero {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α] {f : ι → α}
   (hf : ∑' i, f i ≠ 0) : Summable f := not_imp_comm.1 tsum_eq_zero_of_not_summable hf


lemma DiscreteDistFunc.summable [d : DiscreteDistFunc Ω] : Summable d.m := by
    exact Summable.of_tsum_ne_zero (by simp [d.hu])

--lemma fun_lem {A : Set Ω} {f : A → ℝ} {g : Ω → ℝ} (hg : g = fun i => if i∈A then f i else 0) (x : A) : f x = g x := by

lemma DiscreteDistFunc.summable_set [d : DiscreteDistFunc Ω] (A : Set Ω) : Summable fun i : A => d.m i := by
    let f := fun i : Ω => d.m i
    set g := fun i : A => d.m i
    have hs : Summable f := by
      unfold_let
      exact Summable.of_tsum_ne_zero (by simp [d.hu])
    exact (summable_subtype_and_compl.mpr hs).left
    --I can't believe I proved this theorem!
    --Now I don't need to add Summable assumptions to my theorems
    --exact? keeps searching but can't find this!

-- Thanks to Yaël Dillies for proving this nice lemma
lemma HasSum.of_tsum_ne_zero {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α] {f : ι → α}
   (hf : ∑' i, f i ≠ 0) : HasSum f (∑' i, f i) := by
  obtain ⟨x, hx⟩ : Summable f := Summable.of_tsum_ne_zero hf
  rwa [hx.tsum_eq]

theorem tsum_ofReal_eq {f : α → ℝ} (hs : Summable f) (hp : ∀a, f a ≥ 0):
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  let g : α → NNReal := fun a => (f a).toNNReal
  have hsg : Summable g := by exact Summable.toNNReal hs
  have h1 : ENNReal.ofReal (∑' (a : α), f a) ≠ ⊤ := by exact ENNReal.ofReal_ne_top
  have h2 : ∑' (a : α), ENNReal.ofReal (f a) ≠ ⊤ := by exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsg
  rw [← ENNReal.toReal_eq_toReal h1 h2]
  rw [ENNReal.tsum_toReal_eq]
  rw [ENNReal.toReal_ofReal]
  have he (a : α) : f a = (fun a => (ENNReal.ofReal (f a)).toReal) a := by
    simp
    rw [ENNReal.toReal_ofReal ]
    exact hp a
  rw [tsum_congr he]
  exact tsum_nonneg hp
  exact fun a ↦ ENNReal.ofReal_ne_top

noncomputable
def DiscreteDistFunc.toPMF (d : DiscreteDistFunc Ω) : PMF Ω := {
  val := fun ω : Ω => ENNReal.ofReal (d.m ω)
  property := by
    let f : Ω → ENNReal := fun ω : Ω => ENNReal.ofReal (d.m ω)
    have hz : ∑' (ω : Ω), d.m ω ≠ 0 := by
      simp [d.hu]
    have hnt (ω : Ω) : ENNReal.ofReal (d.m ω) ≠ ⊤ := by
      aesop
    have h3 : ∑' (ω : Ω), f ω = ENNReal.ofReal (∑' (ω : Ω), d.m ω) := by
      unfold_let
      simp
      rw [tsum_ofReal_eq (Summable.of_tsum_ne_zero hz)]
      exact hp
    have hs : ∑' (ω : Ω), f ω = 1 := by
      simp_all only [ne_eq, f]
      simp [ENNReal.tsum_toReal_eq hnt]
      exact hu
    have hz2 : ∑' (ω : Ω), f ω ≠ 0 := by
      simp [hs]
    rw [← hs]
    simp [HasSum.of_tsum_ne_zero hz2]
}

noncomputable
def DiscreteDistFunc.toMeasure (d : DiscreteDistFunc Ω) [MeasurableSpace Ω] : Measure Ω :=
  d.toPMF.toMeasure

-- Example 1.7
namespace Example_1_7

inductive Coin2 where
  | HH
  | HT
  | TH
  | TT
  deriving Fintype

open Coin2

noncomputable
instance dist : DiscreteDistFunc Coin2 := {
  m := fun (x : Coin2) => 1/4
  hp := by simp
  hu := by
    rw [one_div, tsum_const]
    have hc : Nat.card Coin2 = 4 := by aesop
    rw [hc]
    norm_num
  hc := by exact Finite.to_countable
}

lemma dist_pairwise : Pairwise (fun (x y : Coin2) => dist.m x = dist.m y) := by
  exact fun ⦃i j⦄ ↦ congrFun rfl

def E : Finset Coin2 := ⟨{HH,HT,TH},by simp⟩

example : @P _ dist (E : Set Coin2) = 3/4 := by
  rw [P, dist]
  aesop

def F : Finset Coin2 := ⟨{HH,HT},by simp⟩

example : @P _ dist (F : Set Coin2) = 2/4 := by
  rw [P, dist]
  aesop

end Example_1_7

--Theorem 1.1
--1
theorem P_positivity [d : DiscreteDistFunc Ω] (E : Set Ω) (hsumE : Summable fun i : E ↦ d.m ↑i):
  P E ≥ 0 := by
  unfold P
  have hp (ω : E) : d.m ω ≥ 0 := by
    exact d.hp ↑ω
  calc
    ∑' (ω : ↑E), d.m ↑ω ≥ ∑' (i : ↑E), 0 := by rel [(tsum_le_tsum hp (summable_zero) (hsumE))]
    _ ≥ 0 := by simp

--2
theorem P_eq_one [d : DiscreteDistFunc Ω]:
  P (Set.univ : Set Ω) = 1 := by
  exact DistFunc.hu

--3
theorem P_le_of_subset [d : DiscreteDistFunc Ω] (E : Set Ω) (F : Set Ω) (hss : E ⊂ F)
  (hsumE : Summable fun i : E ↦ d.m ↑i)
  (hsumF : Summable fun i : F ↦ d.m ↑i):
  P E ≤ P F := by
  unfold P
  have hs : E ⊆ F := subset_of_ssubset hss
  let e : E → F := fun x => ⟨x,by aesop⟩
  have hi : Function.Injective e := by
    unfold Function.Injective
    aesop
  have h1 : ∀ c ∉ Set.range e, 0 ≤ d.m c := fun c _ ↦ d.hp ↑c
  have h2 : ∀ (i : E), d.m i ≤ d.m (e i) := fun i ↦ Preorder.le_refl (d.m ↑i)
  exact tsum_le_tsum_of_inj e hi h1 h2 hsumE hsumF

--4
theorem P_union_disjoint [d : DiscreteDistFunc Ω] (A : Set Ω) (B : Set Ω)
  (hd : Disjoint A B)
  (hsumA : Summable fun i : A ↦ d.m ↑i)
  (hsumB : Summable fun i : B ↦ d.m ↑i):
   P (A ∪ B) = P A + P B := by
  unfold P
  exact tsum_union_disjoint hd hsumA hsumB

--5
theorem P_compl [d : DiscreteDistFunc Ω] (A : Set Ω)
  (hsum : Summable fun i : A ↦ d.m ↑i)
  (hsumc : Summable fun i : (Set.compl A) ↦ d.m ↑i):
   P (Aᶜ) = 1 - P (A) := by
  rewrite [← (@P_eq_one Ω d)]
  rewrite [(Set.compl_union_self A).symm]
  rewrite [P_union_disjoint]
  simp
  exact Set.disjoint_compl_left_iff_subset.mpr fun ⦃a⦄ a ↦ a
  exact hsumc
  exact hsum

lemma P_empty [DiscreteDistFunc Ω] : P (∅ : Set Ω) = 0 := by
  rw [P]
  exact tsum_empty

open Finset
--Theorem 1.2
theorem P_fin_pairwise_disjoint_union [d : DiscreteDistFunc Ω]
  (n : ℕ)
  (A : ℕ → Set Ω)
  (hpd : (range n : Set ℕ).Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ range n , A i) = ∑ i ∈ (range n), P (A i) := by
  unfold P
  dsimp
  rw [tsum_finset_bUnion_disjoint hpd (by exact fun i _ ↦ hsum i)]

--Some modified versions
theorem P_fin_pairwise_disjoint_union2 [d : DiscreteDistFunc Ω]
  (n : ℕ)
  (I : Finset (Fin n))
  (A : (Fin n) → Set Ω)
  (hpd : Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ I, A i) = ∑' (i : I), P (A i) := by
  unfold P
  have hpd2 : (I : Set (Fin n)).Pairwise (Disjoint on A) := by
    rw [Pairwise] at hpd
    intro x _ y _
    exact fun a ↦ hpd a
  dsimp
  rw [tsum_finset_bUnion_disjoint hpd2 (by exact fun i _ ↦ hsum i)]
  rw [←(Finset.tsum_subtype I (fun i => (∑' (x : ↑(A i)), d.m ↑x)))]

theorem P_fin_pairwise_disjoint_union3 [d : DiscreteDistFunc Ω]
  (n : ℕ)
  (I : Finset (Fin n))
  (A : (Fin n) → Set Ω)
  (hpd : (I : Set (Fin n)).Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ I, A i) = ∑' (i : I), P (A i) := by
  unfold P
  dsimp
  rw [tsum_finset_bUnion_disjoint hpd (by exact fun i _ ↦ hsum i)]
  rw [←(Finset.tsum_subtype I (fun i => (∑' (x : ↑(A i)), d.m ↑x)))]

theorem P_fin_pairwise_disjoint_union4 [d : DiscreteDistFunc Ω]
  (n : ℕ)
  (A : (Fin n) → Set Ω)
  (hpd : Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i , A i) = ∑' i , P (A i) := by
  have hpd2 : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise (Disjoint on A) := by
    rw [Pairwise] at hpd
    intro x _ y _
    exact fun a ↦ hpd a
  have hu : (⋃ i , A i) = ⋃ i ∈ Finset.univ, A i := by simp
  unfold P
  rw [hu]
  dsimp
  rw [tsum_finset_bUnion_disjoint hpd2 (by exact fun i _ ↦ hsum i)]
  exact Eq.symm (tsum_fintype fun b ↦ ∑' (ω : ↑(A b)), d.m ↑ω)

--Theorem 1.3
theorem P_fin_pairwise_disjoint_inter [d : DiscreteDistFunc Ω]
  (n : ℕ) (A : ℕ → Set Ω)
  (hpd : (Finset.range n : Set ℕ).Pairwise (Disjoint on A))
  (huniv : Set.univ = (⋃ i ∈ range n, A i)) (E : Set Ω)
  (hsumEA : ∀j , Summable fun i : ↑(E ∩ A j) ↦ d.m ↑i):
    P E = ∑ i ∈ range n, P (E ∩ A i) := by
  let B : ℕ → Set Ω := fun i => E ∩ A i
  have hpdB : (Finset.range n : Set ℕ).Pairwise (Disjoint on B) := by
    unfold_let
    intro x xin y yin xy
    rw [Function.onFun_apply]
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← Set.inter_inter_distrib_left]
    replace hpd : (Disjoint on A) x y := by exact hpd xin yin xy
    rw [Function.onFun_apply] at hpd
    rw [Set.disjoint_iff_inter_eq_empty] at hpd
    simp_all only [Set.disjoint_iUnion_left, ne_eq, Set.inter_empty]
  have hsumB : ∀j , Summable fun i : B j ↦ d.m ↑i := by exact fun j ↦ hsumEA j
  have hu : ⋃ i ∈ range n, B i = E := by
    unfold_let
    simp only
    calc
    ⋃ i ∈ range n, E ∩ A i = E ∩ (⋃ i ∈ range n, A i) := by exact Eq.symm (Set.inter_iUnion₂ E fun i _ ↦ A i)
    _ = E ∩ Set.univ := by exact congrArg (Inter.inter E) (id (Eq.symm huniv))
    _ = E := by simp
  rw [← P_fin_pairwise_disjoint_union n B hpdB hsumB]
  rw [hu]

--Corollary 1.1
theorem P_inter_add_compl [d : DiscreteDistFunc Ω]
  (A : Set Ω) (B : Set Ω)
  (hsum : Summable fun i : (Set.inter A B) ↦ d.m ↑i)
  (hsumc : Summable fun i : (Set.inter A Bᶜ) ↦ d.m ↑i):
    P A = P (A ∩ B) + P (A ∩ Bᶜ) := by
  let B' (i : ℕ) : Set Ω :=
    match i with
    | 0 => B
    | 1 => Bᶜ
    | _ => ∅
  have hpd : (Finset.range 2 : Set ℕ).Pairwise (Disjoint on B') := by
    intro x xin y yin xy
    rw [Function.onFun_apply]
    have h1 : Disjoint B Bᶜ := Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a ↦ a
    have h2 : Disjoint Bᶜ B := id (Disjoint.symm h1)
    aesop
  have huniv : Set.univ = ⋃ i ∈ range 2, B' i := by
    rw [range_succ]
    simp_all only [coe_range, range_one, mem_insert, mem_singleton, Set.iUnion_iUnion_eq_or_left,Set.iUnion_iUnion_eq_left, Set.compl_union_self, B']
  have hsumB' : ∀j, Summable fun (i : @Inter.inter (Set Ω) _ A (B' j)) ↦ d.m ↑i := by
    intro j
    match j with
      | 0 => exact hsum
      | 1 => exact hsumc
      | x+2 =>
        have hx2 : B' (x+2) = ∅ := rfl
        rw [hx2]
        rw [Set.inter_empty A]
        simp [summable_empty]
  rw [P_fin_pairwise_disjoint_inter 2 B' hpd huniv A hsumB']
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

-- Need this for theorem 1.4
theorem P_sdiff [d : DiscreteDistFunc Ω]
  (A : Set Ω) (B : Set Ω):
    P (A \ B) = P A - P (A ∩ B) := by
  have hd : Disjoint (A \ B) (A ∩ B) := by exact Set.disjoint_sdiff_inter
  have hu : A = (A \ B) ∪ (A ∩ B) := by exact Eq.symm (Set.diff_union_inter A B)
  rw [@eq_sub_iff_add_eq]
  rw [← P_union_disjoint (A \ B) (A ∩ B) hd (d.summable_set (A \ B)) (d.summable_set (A ∩ B))]
  rw [← hu]

--Theorem 1.4
theorem P_union [d : DiscreteDistFunc Ω]
  (A : Set Ω) (B : Set Ω):
    P (A ∪ B) = P A + P B - P (A ∩ B) := by
  let C (i : ℕ) : Set Ω :=
    match i with
    | 0 => A \ B
    | 1 => A ∩ B
    | 2 => B \ A
    | _ => ∅
  have hpd : (Finset.range 3 : Set ℕ).Pairwise (Disjoint on C) := by
    intro x xin y yin xy
    rw [Function.onFun_apply]
    simp [C]
    have hd1 : Disjoint (A \ B) (A ∩ B) := by exact Set.disjoint_sdiff_inter
    have hd2 : Disjoint (A \ B) (B \ A) := by exact disjoint_sdiff_sdiff
    have hd3 : Disjoint (B \ A) (A ∩ B) := by rw [Set.inter_comm] ; exact Set.disjoint_sdiff_inter
    have hd4 : Disjoint (A ∩ B) (A \ B) := by rw [disjoint_comm] ; exact hd1
    have hd5 : Disjoint (A ∩ B) (B \ A) := by exact id (Disjoint.symm hd3)
    have hd6 : Disjoint (B \ A) (A \ B) := by exact id (Disjoint.symm hd2)
    aesop
  have hsum : ∀ (j : ℕ), Summable fun i : C j ↦ d.m ↑i := by exact fun j ↦ DiscreteDistFunc.summable_set (C j)
  have hu : A ∪ B = ⋃ i ∈ range 3, C i := by
    rw [range_succ]
    rw [range_succ]
    aesop
  rw [hu]
  rw [P_fin_pairwise_disjoint_union 3 C hpd hsum]
  rw [sum_range_succ]
  rw [sum_range_succ]
  rw [sum_range_succ]
  unfold_let
  simp
  rw [P_sdiff A B]
  rw [P_sdiff B A]
  rw [Set.inter_comm]
  ring

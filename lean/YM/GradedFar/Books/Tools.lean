import YM.GradedFar.Moving.Cash

/-!
# Compact continuum receipts in the C5 parameters (in particular W system, not H yet).

State hypotheses literally needed, without claiming they're available in kernel construction.
See client's assumptions vs natural language below. -/
namespace YM.FVA2.GradedFar.Books
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
open Reg.Point (stepV)

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (F : (d:ℕ)→Pose.Plans G d) (Y : (d:ℕ)→ℝ→ Prediction G d)
local notation "θ"=>Pose.kinetic N (F 6)
local notation "ψ"=> GroupS.ψ N.criterion M ν

/-- Needs C5 on particular **finite** rosters, at the two physical d,6 once
proxies appointed. Read on the unselected (Steep) book, all at `r`. Fields
`v` on this compact Near input board, use with proxy and `S_*` widths/corrections.
Also all the determining positions of the screen -- same parameters there.
C5 includes those poses. F3 is not stipulated for this clock. -/
def Bought (d : ℕ) {n : ℕ} (K : Set (Points n)) (v : Tags G d n) (p : ℕ) :=
    ∃ (k q:ℕ) (t':ℝ → ℝ) (D':ℝ → Normalize.Change G 6) (E':ℝ → Normalize.Change G d), 2≤k ∧ p+1≤k ∧ k≤q ∧
      Tendsto (fun r=>t' r/g r) τ (𝓝 1) ∧ Tendsto (fun r=>guide G 6 (D' r)) τ (𝓝 0) ∧
      Tendsto (fun r=>guide G d (E' r)) τ (𝓝 0) ∧ RawCalibration N (F 6) t' k q D' ∧
      (∀ i:Fin (N.store.survey d).n, let w := (N.store.survey d).scope i;
       Confirmed N (F d) q k t' E' (tsupport w.t) w.p) ∧ Confirmed N (F d) q k t' E' K v

def Latest := ∀ d n p (v : Tags G d n) (K : Set (Points n)), IsCompact K→ K⊆conf n→ Bought N F d K v p

variable {K : Set (Points n)} (hK : IsCompact K) (hx : K⊆conf n) (v : Tags G d n) (hk : Bought N F d K v p)
variable (hs : ∀ d,Held N (Y d) (F d))
include H hK hx hs hk

section path
variable (r : I → ℝ) (hr : Tendsto r T τ) {x : I→ Points n}(he : ∀ i, x i∈K)
include hr he
/-- Give receipts including θ calibration, transferring arbitrary fixed-age ratio t'∼g.
Includes lower-order crops `p`. -/
theorem contracts :
    Tendsto (fun r=> θ r/g r) τ (𝓝 1) ∧
    Pays T (fun i=> F d (r i) n (x i) v) (fun i=> tells (Pose.line N (x i) v)) (g ∘r) p (fun i=>(θ (r i):ℂ)) := by
  obtain ⟨k,q,u,D,E,h0,hp,hq,hu,hD,hE,Hθ,H0,Hx⟩:=hk
  have hΓ l n x : ∀ᶠ r in τ, ContinuousOn (fun p=> F l r n p x) (conf n) := (show ∀ᶠ r in τ, 0 < r from self_mem_nhdsWithin).mono (fun r h=>(hs l).cont _ h n x)
  have hc l n (x : Tags G l n) (t : Test n): ∀ᶠ r in τ, Y l r n t x=t.applyTo (fun p=> F l r n p x) :=
    (show ∀ᶠ r in τ, 0 < r from self_mem_nhdsWithin).mono (fun r h=>(hs l).full _ h n x t)
  obtain ⟨C,hC,hΘ⟩:= (Pose.F3 N M (F 6) u hu H (Y 6) D (hΓ 6) (hc 6) (hs _).fixed hD q k (by omega) (by omega) Hθ).2.2
  have hf:= relative_reading simple θ u hu k h0 C hΘ
  refine ⟨hf,beauty T N M r hr H _ hK hx (Eventually.of_forall he) v,?_⟩
  have hX:= pinned N M hK hx E u H v q k hu (landed N M (Y d) E u (hΓ d) (hc d) (hs d).fixed (N.store.survey d) H (tainted N M u H hu) hE q k H0) Hx
  have ht:= jet_level T ((shrink simple).comp hr)
  let y i:= Pose.line N (x i) v
  let t i:ℂ:=θ (r i); let t' i:ℂ:= u (r i); let a i:= tells (y i);
  have he' : Till T a (g ∘r) q:= beauty T N M r hr H _ hK hx (Eventually.of_forall he) v
  have hw: Buys T (fun i=>F d (r i) n (x i) v- blend (a i) q (t' i)) (g∘r) k := by
    apply (IsBigO.comp_tendsto hX
      (show Tendsto (fun i=>(r i,(⟨x i,he i⟩:↥K))) T (comap Prod.fst τ) from tendsto_comap_iff.mpr hr)).congr_left
    intro i
    exact congr_arg (fun z : ℂ => F d (r i) n (x i) v - z) (crop_by (y i) q (u (r i)))
  have hA:= hr.eventually (positive_g simple)
  have hh:= budget_growth T hw _ hp ht
  have hb : Buys T (fun i=> t i-t' i) (g ∘r) k := by
    apply budget_of T _ (hA.mono (fun i h=>h.le)) (C:=C); filter_upwards [hr.eventually hΘ] with i hi
    unfold t t'; rwa [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht' : Buys T t' (g∘r) 1:= measuring T N M r hr H u hu
  have p' : Buys T t (g∘r) 1:= measuring T N M r hr H θ hf
  have hT (j : ℕ) : Buys T (fun i=> t i^j-t' i^j) (g∘r) k := by
    induction j with
    | zero=> simp_rw [pow_zero,sub_self]; exact isBigO_zero ..
    | succ j ih =>
      have hr := times_cost T ih (budget_growth T p' 0 zero_le_one ht)
      have hp:=times_cost T hb (budget_growth T (budget_pow T ht' j) 0 (Nat.zero_le _) ht)
      refine (hr.add hp).congr_left (fun i=>?_); rw [pow_succ,pow_succ]; ring
  have ht'' : Buys T (fun i=> blend (a i) q (t i) - blend (a i) q (t' i)) (g∘r) k := by
    unfold blend; simp_rw [← Finset.sum_sub_distrib, ← sub_smul]; apply IsBigO.sum; intro j hj
    exact budget_times_smul T (hT j) (he' _ (Finset.mem_range_succ_iff.mp hj))
  have hon : Buys T (fun i=> blend (a i) q (t i)-blend (a i) p (t i)) (g∘r) (p+1) := by
    let H' := Finset.Ico (p+1) (q+1); have hl : p+1≤q+1:=by omega
    have hv i : blend (a i) q (t i)-blend (a i) p (t i)=∑ j∈ H', t i^j • a i j := by
      unfold H' blend
      rw [Finset.sum_Ico_eq_sub _ hl]
    simp_rw [hv]; apply IsBigO.sum; intro i hi; have hv:= Finset.mem_Ico.mp hi; exact budget_times_smul T
      (budget_growth T (budget_pow T p' i) (p+1) hv.1 ht) (he' i (Nat.lt_succ_iff.mp hv.2))
  refine ((hh.sub (budget_growth T ht'' (p+1) hp ht)).add hon).congr_left (fun i=>?_); unfold a t' y t; abel
end path

omit hk hK hx in
lemma begin (h' : Latest N F) : Beginning N θ d (F d) := by
    intro n p K hK hx u
    have he:= (contracts (comap (Prod.fst : ℝ × ↥K→ℝ) τ) N M H F Y hK hx u (h' d n p u K hK hx) hs Prod.fst tendsto_comap (x:=fun i=>i.2.val) (fun i=>i.2.property)).2
    apply he.2.congr_left
    intro i
    exact congr_arg (fun z : ℂ => F d i.1 n i.2.val u - z) (crop_by (Pose.line N i.2.val u) p (θ i.1)).symm
omit hk hK hx in
lemma heated (h' : Latest N F) : Tendsto (fun r=> θ r/g r) τ (𝓝 1) := by
    let v: Tags G 6 1:=0; let K:Set (Points 1):={0}; have hK: IsCompact K:= isCompact_singleton
    have hx : K⊆conf 1:= singleton_subset_iff.mpr (fun _ _ _=> Subsingleton.elim ..)
    exact (contracts τ N M H F Y hK hx v (h' 6 1 1 v K hK hx) hs (fun i=>i) tendsto_id (x:=fun _=>0) (fun _=> mem_singleton _)).1
end
end YM.FVA2.GradedFar.Books

import YM.WilsonCoeffUV.Root.UV.GaugeSupply
import YM.WilsonCoeffUV.Wick.Limit
/-!
# Install with addressed Wick optional budget at every arbitrary horizon/order request.
Precomputed Clockétique. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain PathCost Supply Ticket Next.Foundations
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' b m N M r:ℕ}{F:Labels.Frame G h} {H:Hol G} {T:SectionData F}
variable {z ξ σ A' B:ℝ} {s t:ℝ}{E W C C':Credit}{pf:h<D}
open Real
variable (H) (R:Master H)
-- generic grouped-bill receipts add at witness selection. fixed parameters H etc.
def axiomata {α:Type*} (F:α→ℝ) (S:Finset α):= ∑ i∈S, |F i|
lemma gains (S:Finset α)(F:α→ℝ)(x:α)(h:x∈S): F x≤axiomata F S:= (le_abs_self ..).trans (Finset.single_le_sum (fun x _=>abs_nonneg (F x)) h)
def utopia (K:KernelChoices)(_A D d:ℕ) : ℝ :=
    axiomata (fun i:ℕ=>if hi:4 ≤ i then
      exp (exp (weightΩ K.penalty i hi)) +
      if p:5 ≤ d then
        let s:=splash G K i d hi p; let F h := R.F h; let X:= Finset.range (d+1)
        ∑ h∈ X, axiomata (fun j=> exp (exp (wellfare G j h s))+
                 ∑ v∈ Finset.range (D+1), exp (exp (threeP (F h) v (s/2) (half_pos (spatter G K i d hi p).1) j))) X
      else 0 else 0) (Finset.range (d+1))

lemma partsU (K:KernelChoices)(A D' d:ℕ) {i:ℕ}(h':4 ≤ i)(p:5 ≤ d)(hv:i ≤ d)(y:ℝ)(hy:utopia H R K A D' d ≤ y)(he:h ≤ d)(hp:D≤ D') : exp (exp (weightΩ K.penalty i h')) ≤ y ∧
    ∀ j≤h,let s:=splash G K i d h' p; exp (exp (wellfare G j h s)) ≤ y ∧ exp (exp (threeP (R.F h) D (s/2) (half_pos (spatter G K i d h' p).1) j))≤y:=by
    unfold utopia at hy; let X n:=Finset.range (n+1); let s:=splash G K i d h' p
    have hz:= (gains _ _ i (show i∈Finset.range (d+1) from Finset.mem_range.mpr (by omega))).trans hy
    simp only [dif_pos h',dif_pos p] at hz
    let T h j k:=exp (exp (threeP (R.F h) k (s/2) (half_pos (spatter G K i d h' p).1) j))
    let M h j:= ∑ v∈ X D', T h j v
    let V h j:= exp (exp (wellfare G j h s))
    let A h:= axiomata (fun j=> V h j+ M h j) (X d)
    have hp' h j :0≤M h j:= Finset.sum_nonneg fun i _=> (exp_pos _).le
    have ht h: 0≤ A h:= Finset.sum_nonneg fun _ _=> abs_nonneg _
    refine ⟨(le_add_of_nonneg_right (show 0≤∑ j∈ X d,A j from Finset.sum_nonneg fun i _=> ht i)).trans hz,fun j hj=>?_⟩; intro S
    have he :V h j+M h j≤ y:= (gains _ (fun j=> V h j+M h j) j (Finset.mem_range.mpr (by omega) : j∈ X d)).trans ((Finset.single_le_sum (f:=A) (fun i _=>ht i) (Finset.mem_range.mpr (by omega):h∈ X d)).trans ((le_add_of_nonneg_left (exp_pos _).le).trans hz))
    exact ⟨(le_add_of_nonneg_right (hp' h j)).trans he,(Finset.single_le_sum (f:=T h j) (fun _ _=>(exp_pos _).le) (Finset.mem_range.mpr (by omega) : D∈ X D')).trans ((le_add_of_nonneg_left (exp_pos _).le).trans he)⟩
lemma embargo (A:Levels G)(h:exp (exp z) ≤ A.clock.hatBeta m):z≤ zz A m:=by
    have h:=Real.log_le_log (exp_pos _) h; rw [Real.log_exp] at h; have hv:=Real.log_le_log (exp_pos _) h; rw [Real.log_exp] at hv; exact hv.trans (le_add_of_nonneg_left zero_le_one)
section
variable {Pr:Sheet G}{Q:Rolls Pr}{Ω: Protection Q}{Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}{A:Levels G}{Ñ:ChartRatio G}{F' D':ℕ→ℕ}
lemma figures_cover (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G Pr.kernel F'≤ Pr.floorL)(zL:(fun i=>sharp H R Pr.kernel Ñ i (F' i) (D' i))≤ Pr.floorL)
    {y:ℕ→ℝ}(a:BasicBill Y A y m)(hp:voucher Q F' Ñ ≤ Y.betaEntry)(hz:(fun j=>tickZ H R Pr.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)
    (hr:(fun j=> utopia H R Pr.kernel (F' j) (D' j) j)≤ Y.betaEntry)(x:h<D)(u:∀ j≥ m, let k:=A.clock.J (j+1);5≤ k∧h+1≤k-2∧e+1≤F' k ∧ D≤ D' k):∃ W:ChorusLine H
    (R.T h) x e Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧W.arch.V.y=y
    ∧W.arch.V.anchor=m ∧ Weston W.arch Credit.leanC ∧ (∀ j (v:W.arch.V.anchor≤j), ∃ (x:h+1≤A.clock.J (j+1)-2) (u:5≤A.clock.J (j+1)) (q:craftQuest A j (F' (A.clock.J (j+1))) u)(s:roomV A j u), W.arch.angle j v=liftWing Ñ x q s) :=by
    obtain ⟨S,hpS,gS,v,w,q⟩:= fixtures_covered H R g hA pL zL hp hz x e m a u
    have hG (j)(hv:m≤j):= u j hv
    have h' j (_g:S.arch.V.anchor≤j) : S.arch.V.cash Credit.leanC j= y j :=by rw [cash,v,Credit.lean_cost]
    have hh j (hn:S.arch.V.anchor≤ j) := ((partsU H R A.clock.kernel (F' (A.clock.J (j+1))) (D' (A.clock.J (j+1))) _ (A.clock.adm j) (u j (w ▸ hn)).1 (A.fits.mono j.le_succ) (exp (exp (y j-1))) (by rw [a.kernel];exact (hr _).trans (a.pays j (w ▸ hn))) (h:=_) (i:=_) (show h ≤ _ from Nat.le_of_succ_le (le_trans (u j (w ▸ hn)).2.1 (Nat.sub_le ..))) (u j (w ▸ hn)).2.2.2))
    refine ⟨_,hpS,gS,v,w,⟨?_,?_,?_⟩,q⟩
    · intro j n; subst A; rw [h' j n]; exact redeemBill (hh _ n).1
    · intro j n r hr; obtain ⟨a,b,d,xs,z⟩:= q j n; rw [h' _ n,z]; exact redeemBill ((hh _ n).2 _ hr).1
    intro j n r hr; obtain ⟨a,b,d,xs,z⟩:= q j n; rw [h' _ n,z];
    exact redeemBill ((hh _ n).2 _ hr).2
lemma figures (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G Pr.kernel F'≤ Pr.floorL)(zL:(fun i=>sharp H R Pr.kernel Ñ i (F' i) (D' i))≤ Pr.floorL)
    (a:Paid b' A)(hp:voucher Q F' Ñ ≤ Y.betaEntry)(hz:(fun j=>tickZ H R Pr.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)
    (hr:(fun j=> utopia H R Pr.kernel (F' j) (D' j) j)≤ Y.betaEntry)(x:h<D)(u:∀ j≥ m, let k:=A.clock.J (j+1);5≤ k∧h+1≤k-2∧e+1≤F' k ∧ D≤ D' k):∃ W:ChorusLine H
    (R.T h) x e Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧W.arch.V.y=zz A
    ∧W.arch.V.anchor=m ∧ Weston W.arch Credit.leanC ∧ (∀ j (v:W.arch.V.anchor≤j), ∃ (x:h+1≤A.clock.J (j+1)-2) (u:5≤A.clock.J (j+1)) (q:craftQuest A j (F' (A.clock.J (j+1))) u)(s:roomV A j u), W.arch.angle j v=liftWing Ñ x q s) :=by
    exact figures_cover H R g hA pL zL (booked g a hp m) hp hz hr x u
end
end YM.WilsonCoeffUV.Cosmos.Polestar

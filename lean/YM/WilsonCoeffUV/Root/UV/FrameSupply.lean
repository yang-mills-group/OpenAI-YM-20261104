import YM.WilsonCoeffUV.Root.UV.Aperture
/-!
# Copy budget installer all orders through a horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Supply Ticket
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}

-- dictionary master. Hens any list. unit included as chosen horizon.
structure Master (H:Hol G) where
    F (h:ℕ): Frame G h
    T (h:ℕ): SectionData (F h)
    spec h: (T h).Sound H
    pop h: Bid.pop (T h)
variable {Ñ:ChartRatio G} (H) (R:Master H)
-- simultaneous max demands at h≤ j-3, D≤ exponential nD(j). pre-block including widths.
def slopeV (H:Hol G)(F:Frame G h)(K:KernelChoices)(p:h<D)(Ñ:ChartRatio G)(e j:ℕ):= (eventually_atTop.mp (preSpaced F H Ñ K p e j)).choose
def sharp (K:KernelChoices)(Ñ:ChartRatio G)(j F D:ℕ):= ∑ h∈ Finset.range (j+1),∑ i∈ Finset.range (F+1),∑ d∈Finset.range (D+1),if p:h<d then slopeV H (R.F h) K p Ñ i j else 0
lemma sharpH (Ñ:ChartRatio G)(K:KernelChoices){d}(p:h<D)(v:h≤j)(z:D≤d)(e F)(q:e≤F): slopeV H (R.F h) K p Ñ e j≤ sharp H R K Ñ j F d := by
   let T h i u:= if t:h<u then slopeV H (R.F h) K t Ñ i j else 0
   let S i:=Finset.range (i+1)
   change _≤ ∑ h∈ S j,∑ i∈ S F,∑ u∈S d,T h i u
   rw [← show T h e D= _ from dif_pos p]; exact (Finset.single_le_sum (fun i _=>Nat.zero_le (T h e i)) (show D∈S d from Finset.mem_range.mpr (by omega))).trans ((Finset.single_le_sum (fun i _=>Nat.zero_le (∑ u∈ S d,T h i u)) (show e∈ S F from Finset.mem_range.mpr (by omega))).trans (Finset.single_le_sum (fun h _=>Nat.zero_le (∑ i∈ S F,∑ u∈S d,T h i u)) (show h∈S j from Finset.mem_range.mpr (by omega))))
-- after length
def sunL (K:KernelChoices)(L:Side)(Ñ:ChartRatio G)(H:Hol G)(F0:SectionData F)(p:h<D)(e e' j:ℕ):= (eventually_atTop.mp (locks Ñ K L H F0 p j e e')).choose
open Real
def tickZ (K:KernelChoices)(Ñ:ChartRatio G)(L:Side)(F D j:ℕ):= ∑ h∈Finset.range (j+1),∑ i∈Finset.range (F+1),∑ d∈Finset.range (D+1),if p:h<d then exp (exp (sunL K L Ñ H (R.T h) p i F j)) else 0
lemma tax_after (K:KernelChoices)(L:Side)(Ñ:ChartRatio G)(p:h<D){e e' j d:ℕ}(q:h≤j)(r:e≤e')(g:D≤d): exp (exp (sunL K L Ñ H (R.T h) p e e' j)) ≤ tickZ H R K Ñ L e' d j:=by
    let T h i d:= if v:h<d then exp (exp (sunL K L Ñ H (R.T h) v i e' j)) else 0
    let S i:=Finset.range (i+1)
    have he h i d : 0≤ T h i d:=by unfold T; split; positivity; exact le_rfl
    rw [← show T h e D= _ from dif_pos p]
    exact (Finset.single_le_sum (fun i _=>he h e i) (show D∈ S d from Finset.mem_range.mpr (by omega))).trans ((Finset.single_le_sum (fun i _=> Finset.sum_nonneg (s:=S d) (fun j _=> he h i j)) (show e∈ S e' from Finset.mem_range.mpr (by omega))).trans (Finset.single_le_sum (fun h _=>Finset.sum_nonneg (s:=S e') (fun i _=> Finset.sum_nonneg (s:=S d) (fun j _=> he h i j))) (show h∈ S j from Finset.mem_range.mpr (by omega))))

variable {p:Sheet G}{Q:Rolls p}{Ω:Protection Q}{F' D':ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}
lemma fixtures_covered (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel F'≤ p.floorL)(zL:(fun i=>sharp H R p.kernel Ñ i (F' i) (D' i))≤ p.floorL){y:ℕ→ℝ}(hp:voucher Q F' Ñ≤ Y.betaEntry)(hz:(fun j=> tickZ H R p.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)
    (X:h<D)(e' i:ℕ)(a:BasicBill Y A y i)(hu:∀ j≥i, let k:= A.clock.J (j+1); 5≤k ∧ h+1≤k-2 ∧ e'+1 ≤ F' k ∧ D≤ D' k):∃ W:ChorusLine H (R.T h) X e' Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A ∧ W.arch.V.paid=Ñ ∧ W.arch.V.y=y ∧ W.arch.V.anchor=i ∧ (∀ j (v:W.arch.V.anchor≤j), ∃ (x:h+1≤A.clock.J (j+1)-2) (u:5≤A.clock.J (j+1)) (q:craftQuest A j (F' (A.clock.J (j+1))) u)(s:roomV A j u), W.arch.angle j v=liftWing Ñ x q s):=by
    have ht j : A.S.block j=Q.L (A.clock.J (j+1)):= by rw [←A.fits.sameFactor,a.lengths]
    have hh j (p:j≥ i):= afforded a.kernel a.lengths F' pL j ((hu j p).1)
    let P j (v:i≤j):= quest A j Ñ ((hu j v).1) (hh j v)
    have he j (v:i≤ j): Escrow (P j v) (e'+1) (Credit.leanC.buy (y j)):=by
       rw [Credit.lean_cost]; let k:=A.clock.J (j+1)
       have hp': delayCost Q F' Ñ k ≤ y j:= scriptVoucher _ _ _ k (le_trans (hp k) (a.pays j v))
       exact further ((eventually_atTop.mp (deferred p.kernel (Q.L k) k (F' k) Ñ)).choose_spec _ hp' A j a.kernel rfl (ht j) _ _) (hu j v).2.2.1 le_rfl
    let D: Realm G (e'+1) Credit.leanC:= ⟨A,Ñ,g,hA,i, y,a.cut,a.age,P,fun i e=> le_rfl,he⟩
    have hv j (v:i≤j): roomV A j (hu j v).1 ∧∀ x:roomV A j (hu j v).1,underway H (R.F h) X e' (liftWing Ñ (hu j v).2.1 (hh j v) x):=by
       let k:=A.clock.J (j+1); let H':=R.F h; have hb:h≤k:=by change h ≤ A.clock.J (j+1); have ht: h+1≤ A.clock.J (j+1)-2:= (hu j v).2.1; omega
       have hx : slopeV H H' p.kernel X Ñ e' k ≤ (A.S.block j).val:= le_trans ((sharpH H R Ñ p.kernel X hb (hu j v).2.2.2 e' (F' k) (e'.le_succ.trans (hu j v).2.2.1)).trans (zL k)) ((Q.large k).need.trans (by rw [ht j]))
       have he:= (eventually_atTop.mp (preSpaced (R.F h) H Ñ p.kernel X e' k)).choose_spec _ hx A j a.kernel rfl rfl (hu j v).1 (hu j v).2.1; exact ⟨he.1,fun i=>he.2 _ _ _⟩
    let I j (z:i≤j):= liftWing Ñ (hu j z).2.1 (hh j z) (hv j z).1
    have hp j (z:i≤j): Repose H (R.T h) X e' (I j z) (D.cash Credit.leanC j)∧ flagC H (R.F h) X e' (I j z) ≤ D.cash Credit.leanC j:=by
       let k:= A.clock.J (j+1); have hb:h≤k:=by change h≤ A.clock.J (j+1); have ht:h+1≤ A.clock.J (j+1)-2:= (hu j z).2.1; omega
       let A':= sunL p.kernel (Q.L k) Ñ H (R.T h) X e' (F' k) k
       have hZ : exp (exp A') ≤ exp (exp (y j-1)):= ((tax_after H R p.kernel (Q.L k) Ñ X hb (e'.le_succ.trans (hu j z).2.2.1) (hu j z).2.2.2).trans (hz k)).trans (a.pays j z)
       have hP := redeemBill hZ
       have ht' : A'≤ D.cash Credit.leanC j:=by rw [cash,Credit.lean_cost]; exact hP
       exact (eventually_atTop.mp (locks Ñ p.kernel (Q.L k) H (R.T h) X k e' (F' k))).choose_spec _ ht' A j a.kernel rfl (ht j) _ _ (hh j z) (hv j z).1 ((hv j z).2 _)
    let S : Theatre H (R.T h) X e' Credit.leanC Credit.leanC:=⟨D,R.spec _,R.pop _, I,fun i p=> lamplight Ñ _ (hh i p) (hv i p).1,fun i x=> le_rfl,fun i p=>(hp i p).1⟩
    exact ⟨⟨S,fun i p=>(hp i p).2⟩,rfl,rfl,rfl,rfl,fun j v=> ⟨(hu j v).2.1,(hu j v).1,hh j v,(hv j v).1,rfl⟩⟩
lemma fixtures_paid (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel F'≤ p.floorL)(zL:(fun i=>sharp H R p.kernel Ñ i (F' i) (D' i))≤ p.floorL)(a:Paid b' A)(hp:voucher Q F' Ñ≤ Y.betaEntry)(hz:(fun j=> tickZ H R p.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)
    (X:h<D)(e' i:ℕ)(hu:∀ j≥i, let k:= A.clock.J (j+1); 5≤k ∧ h+1≤k-2 ∧ e'+1 ≤ F' k ∧ D≤ D' k):∃ W:ChorusLine H (R.T h) X e' Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A ∧ W.arch.V.paid=Ñ ∧ W.arch.V.y=zz A ∧ W.arch.V.anchor=i ∧ (∀ j (v:W.arch.V.anchor≤j), ∃ (x:h+1≤A.clock.J (j+1)-2) (u:5≤A.clock.J (j+1)) (q:craftQuest A j (F' (A.clock.J (j+1))) u)(s:roomV A j u), W.arch.angle j v=liftWing Ñ x q s):=by
    exact fixtures_covered H R g hA pL zL hp hz X e' i (booked g a hp i) hu
lemma fixtures (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel F'≤ p.floorL)(zL:(fun i=>sharp H R p.kernel Ñ i (F' i) (D' i))≤ p.floorL)(a:Paid b' A)(hp:voucher Q F' Ñ≤ Y.betaEntry)(hz:(fun j=> tickZ H R p.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)
    (X:h<D)(e' i:ℕ)(hu:∀ j≥i, let k:= A.clock.J (j+1); 5≤k ∧ h+1≤k-2 ∧ e'+1 ≤ F' k ∧ D≤ D' k):∃ W:ChorusLine H (R.T h) X e' Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A ∧ W.arch.V.paid=Ñ ∧ W.arch.V.y=zz A ∧ W.arch.V.anchor=i:=by
    obtain ⟨W,h₁,h₂,h₃,h₄,_⟩:= fixtures_paid H R g hA pL zL a hp hz X e' i hu; exact ⟨W,h₁,h₂,h₃,h₄⟩
end YM.WilsonCoeffUV.Cosmos.Polestar

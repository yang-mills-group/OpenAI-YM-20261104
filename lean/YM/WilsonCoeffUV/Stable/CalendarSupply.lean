import YM.WilsonCoeffUV.Stable.PreSchedule
/-! # Realize all revenues on WilsonX formal path with h horizons announcing at same Levels and stamps. Caps Lebesgue receipt σ served before length. Older terminal auxiliary segments budget separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Shard.Plan
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
variable {Pr:Sheet G}{Q:Rolls Pr}{Ω: Protection Q}{Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}{Ñ:ChartRatio G}{F':ℕ→ℕ}
lemma guild (H:Hol G)(R:Master H)(p:h<D)(v:Rails h k u e)(g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G Pr.kernel F'≤ Pr.floorL)(zL:(fun i=>sharp H R Pr.kernel Ñ i (F' i) (F' i))≤ Pr.floorL)(xL:(fun i=>climbP H R Ñ Pr.kernel i (F' i)) ≤ Pr.floorL)(a:Paid b' A)(hp:voucher Q F' Ñ ≤ Y.betaEntry)(hz:(fun j=>tickZ H R Pr.kernel Ñ (Q.L j) (F' j) (F' j) j)≤ Y.betaEntry)(hr:(fun j=> utopia H R Pr.kernel (F' j) (F' j) j)≤ Y.betaEntry)(hR:(fun j=> guardRail H R Ñ Pr.kernel j (F' j) (Q.L j)) ≤ Y.betaEntry)
    (w:∀ j≥ m, let i:=A.clock.J (j+1); 5 ≤ i ∧ h+1≤ i-2 ∧ e+1≤ F' i ∧ D≤ F' i ∧ k≤ F' i ∧ u≤ F' i) : ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch:=by
    obtain ⟨S,hS,vS,x,y,z,t⟩:= figures H R g hA pL zL a hp hz hr p (e:=e) (m:=m) (fun j p=> let V:=w j p; ⟨V.1,V.2.1,V.2.2.1,V.2.2.2.1⟩)
    have hh j (v':S.arch.V.anchor≤j): CompassP H (R.T h) p v (S.arch.angle j v') (S.arch.V.cash Credit.leanC j):=by
       let i:=A.clock.J (j+1); have ht:=w j (y ▸ v'); obtain ⟨a',c,d,q,z⟩:= t j v'
       have hy:A.S.block j=Q.L i:=by rw [← A.fits.sameFactor,a.lengths]
       have hp : climbP H R Ñ Pr.kernel i (F' i) ≤ (A.S.block j).val:= by rw [hy]; exact (xL i).trans (Q.large i).need
       have hQ: guardRail H R Ñ Pr.kernel i (F' i) (A.S.block j) ≤ A.clock.hatBeta j:= by rw [hy]; exact (hR i).trans (a.pays j)
       rw [z,cash,x,Credit.lean_cost]; exact Packing H R Ñ Pr.kernel _ (F' i) A j a.kernel rfl c d q a' hp p v ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 (e.le_succ.trans ht.2.2.1) hQ
    exact ⟨S,⟨S.arch,hh⟩,hS,vS,x,y,z,rfl⟩

lemma truly (H:Hol G) (R:Master H)(p:h<D)(v:Rails h k u e)(g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G Pr.kernel F'≤ Pr.floorL)
    (zL:(fun i=>sharp H R Pr.kernel Ñ i (F' i) (F' i))≤ Pr.floorL)(xL:(fun i=>climbP H R Ñ Pr.kernel i (F' i)) ≤ Pr.floorL)
    (a:Paid b' A)(hp:voucher Q F' Ñ ≤ Y.betaEntry)(hz:(fun j=>tickZ H R Pr.kernel Ñ (Q.L j) (F' j) (F' j) j)≤ Y.betaEntry)
    (hr:(fun j=> utopia H R Pr.kernel (F' j) (F' j) j)≤ Y.betaEntry)(hR:(fun j=> guardRail H R Ñ Pr.kernel j (F' j) (Q.L j)) ≤ Y.betaEntry)
    (z:Tendsto F' atTop atTop): ∀ᶠ m in atTop,∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,
    ∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ
    ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch:=by
    have he: Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨t,h⟩:= eventually_atTop.mp ((he.eventually_ge_atTop (h+5)).and ((z.comp he).eventually_ge_atTop (e+1+D+k+u))); apply (eventually_ge_atTop t).mono; intro i g'
    exact guild H R p v g hA pL zL xL a hp hz hr hR (m:=i) fun j hj=>by obtain ⟨x,h⟩:= h j (g'.trans hj); simp only [Function.comp_apply] at *; omega

-- announce all arbitrary requests. Frontier witness strengthening. formal independent pure. optional any extra demands as joins (use pL solutions later)
theorem FlightsC (H:Hol G)(R:Master H)(Ñ:ChartRatio G)(q:LocalRatio Ñ)(u:ℝ)(hu:0<u)(g:G.Simple) (f:ℕ→ℕ): ∃ p: Sheet G, p.kernel.penalty=u ∧ f≤ p.floorL ∧ Nonempty (Rolls p) ∧∀ W:Rolls p,∀ F:ℕ→ℝ, ∃ T:Protection W,∃ Y:Delays T,F≤ Y.betaEntry ∧ ∃ o:Bar Y, Nonempty (Supply.Wait o) ∧∀ B:Supply.Wait o, (∃ A:Levels G,Paid B A) ∧ ∀ (A:Levels G), Paid B A →
       (∀ e:ℕ,∀ᶠ m in atTop, ∃ S:Realm G e Credit.leanC, S.draws=A ∧ S.paid=Ñ ∧ S.y=zz A ∧ S.anchor=m ∧ Mosaic.Inkplate e S Credit.leanC) ∧
       (∀ e h D k u:ℕ,∀ p:h<D,∀v:Rails h k u e,∀ᶠ m in atTop,∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch):=by
    let X:= @id ℕ; let K:= Next.Foundations.kernel G u hu
    have he:= Next.Foundations.branches G u hu
    obtain ⟨T⟩:= cap_st
    let a:=floors G K X; let b i:= sharp H R K Ñ i (X i) (X i); let c i:= climbP H R Ñ K i (X i)
    let p: Sheet G:= ⟨K,he,fun _=>T,5,by omega,monotone_const,monotone_const,monotone_const, (a⊔b)⊔(c⊔f)⟩
    have hP:a≤p.floorL:= (le_sup_left (b:=b)).trans le_sup_left; have hp:b≤ p.floorL:= (le_sup_right (a:=a)).trans le_sup_left; have hc:c≤p.floorL:= (le_sup_left (b:=f)).trans le_sup_right
    refine ⟨p,(Axial.viable G u hu).choose_spec.1,(le_sup_right (a:=c)).trans le_sup_right,Rolls.exists_rolls p g,fun W F=>?_⟩
    obtain ⟨t,h⟩:= Protection.exists_margin W (fun _=>1) (fun _=>one_pos)
    let L j:=tickZ H R K Ñ (W.L j) (X j) (X j) j
    let V:= voucher W X Ñ; let Z:= Mosaic.accountZ K X Ñ; let z j:=guardRail H R Ñ K j (X j) (W.L j); let R' j:=utopia H R K (X j) (X j) j
    let A:=Z⊔(V⊔ L); let U:=F⊔(z⊔R'); let Y: Delays t:= ⟨A⊔U,0,0,0⟩
    have ha:A≤Y.betaEntry:= le_sup_left; have hu:U≤ Y.betaEntry:= le_sup_right; have hY:V≤A:=(le_sup_left (b:=L)).trans le_sup_right
    obtain ⟨o,h'⟩:= Bar.exists_above Y 1
    refine ⟨t,Y,(le_trans (show F≤U from le_sup_left) hu),o,⟨0,fun _ _=>0,fun _=>by simp,0⟩,?_⟩
    intro B; refine ⟨Wait.ready B g,?_⟩; intro Z₀ T'
    have u0: F≤ Y.betaEntry:=(le_trans (show F≤U from le_sup_left) hu)
    have u1:V≤Y.betaEntry:= hY.trans ha
    have hZ:Z≤Y.betaEntry:= le_trans (show Z≤ A from le_sup_left) ha
    have hL:L≤Y.betaEntry:= le_trans (le_trans (show L≤ V⊔L from le_sup_right) (show V⊔L≤A from le_sup_right)) ha
    have hz:z⊔R'≤Y.betaEntry:= le_trans (show _ ≤ U from le_sup_right) hu
    have hu: R'≤Y.betaEntry:= le_trans le_sup_right hz; have hh:z≤Y.betaEntry:= le_trans le_sup_left hz
    constructor
    · exact Mosaic.proceeds (p:=p) (b':=B) (H:=X) g q hP T' u1 hZ tendsto_id
    intro e h D k u q' t; exact truly H R (Q:=W) (o:=o) (b':=B) q' t g q (F':=X) hP hp hc T' u1 hL hu hh tendsto_id
end YM.WilsonCoeffUV.Shard.Plan

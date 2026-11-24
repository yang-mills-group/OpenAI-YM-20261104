import YM.RGComparison.Core16.Parcel.Ease
/-! # Honest Planet on larger-block at our contours
Includes genuine reality on the MM recursion word test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Parcel.Oven
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Matrix Push.AbsoluteSums.Animals
open Lumen Lumen.Planet PertExtension PertExtension.Series Tested Radial Therm
open Forge Forge.Hut Precision Exterior Push Push.BetaTransport Push.GridApprox Finset
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}{H:Patch}{K:KernelChoices}
variable {d:f.val=c.val*H.L.val} {P:Oven H}{X:Shelf G (PlaqAxes ⊕ Axis) P.Xways} (T:Forest (StepData.mk H K d).ratio)
variable {u:Directions G c}(hP: P.Offers X K)(hu:∀ i,‖u i‖ ≤ X.Q)
local notation "Y"=> parcela K X T u
local notation "S"=> StepData.mk H K d
local notation "R"=> Hut.width H

include hP hu
private lemma payout (hg:H.Branches K G){g:ℝ}(h:amen X g)(i:Rooms c f) (x:Sky G T.Free) (s:(S).Choices) (he:crisp X.δ ((Y).soil i) x) : (Y).cost g s x i=X.U ((Y).glyph i) ((Y).load i g x):=by
    rw [← hP.citations ((Y).glyph i) (mem_closedBall_zero_iff.mpr (load_ok T hP hu h i he))]
    rcases i with i|i
    · change G.price (faceValue (T.drape x) i)=G.price _
      exact congrArg G.price (portAccess K P (U:=T.drape x) (z:=i.1) i.2 (oiled T hP (.inl i) (g:=g) he))
    exact ((glow T hP hu h hg i s he).1).symm

omit hu in
lemma heat_extent (i:T.Free): (Y).heat i=neighborsOf (Hut.pad T) (2*R) (Hut.pad T i):= by obtain ⟨Q,H,h,_⟩:= hP.purchase; change neighborsOf (Hut.pad T) (2*X.sector.b) (Hut.pad T i)=_; rw [h]; rfl
lemma steaming (h:H.Branches K G): ∀ (g:ℝ),amen X g → ∀ i: T.Free, ∀ x y: Sky G T.Free, Planet.AlwaysOff i x y → crisp X.δ ((Y).heat i) x → crisp X.δ ((Y).heat i) y → ∀ s:(S).Choices, (Y).meter g s x=(Y).meter g s y:=by
    intro g hg i x y hM h1 h2 s
    have ht (p:Edge (Site c)): H.frameMass K (expandAt (hold S p.1) (T.drape x)) (s.1 p.1) = H.frameMass K (expandAt (hold S p.1) (T.drape y)) (s.1 p.1) ∧ H.predictorMass K ((S).connector (T.drape x) s.1 p) (s.2 p)= H.predictorMass K ((S).connector (T.drape y) s.1 p) (s.2 p) :=by
        by_cases hz:i∈ (Y).soil (.inr p)
        · have hi:= (Y).in_heat .. |>.1 hz; have he:= (Y).soil_heat hi
          have hX:= glow T hP hu hg h p s (crisp_negligible _ _ le_rfl he h1)|>.2
          have hY:= glow T hP hu hg h p s (crisp_negligible _ _ le_rfl he h2)|>.2
          exact ⟨hX.1.trans hY.1.symm,hX.2.trans hY.2.symm⟩
        rw [geometry T hP] at hz
        have hp:∀ j∈ neighborsOf (Hut.pad T) R (hold S p.1), x j=y j:=fun j hj=> hM j (fun e=>hz (e ▸ hj))
        refine ⟨ (site_dep S h p.1 (wires hp ?_) _).2, congrArg (fun t=> H.predictorMass K t _) (stitch h (s:=s.1) (t:=s.1) rfl rfl hp)⟩
        change separation (hold S p.1) (hold S p.1)+reach H ≤ R; rw [separation_self]; unfold Hut.width; omega
    change (S).likelihood _ _=(S).likelihood _ _; unfold StepData.likelihood; exact congr_arg₂ (·*·) (prod_congr rfl (fun i _=> (ht (i,0)).1)) (prod_congr rfl fun i _=>(ht i).2)
lemma paints (hS:Bid.Larger («S»:=S) (G:=G)): (Y).Steady:=by
    refine ⟨hP.good,?_,budgeting T hP hu,spirit T hP,steaming T hP hu hS.1,fun g=>?_,?_⟩
    · intro g hg; obtain ⟨Q,hQ,h,hx⟩:= hP.purchase
      rw [handed,h]; exact grants T hS hg.1 hQ (fun i=> hx _ (hu i) _ hg)
    · exact payout T hP hu hS.1
    intro g hg j x y s he; rw [geometry T hP] at he
    rcases j with j|j
    · exact congrArg G.price (stele (b:=j) he)
    have hh:= stitch hS.1 (s:=s.1) (t:=s.1) (b:=j) rfl rfl he
    apply congrArg (fun t=> linkEnergy S ((slice u g) j*(H.predict K t (s.2 j))⁻¹)) hh
end YM.RGComparison.Core16.Parcel.Oven

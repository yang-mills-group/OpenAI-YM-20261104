import YM.Integration.WilsonMovingSingletonStock

/-! The dated original singleton account, with its signed old subset and both rooted returns. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim.WilsonMovingSingleton
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open Packets Art Gas Ursell Trees Multiple Letter OmitClusters Stained March Shield Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section crispPaper
variable {J:Teller G} {A: ConnectedActivityE6.Target G J} {Lc:Side} (M:JointLoad.Heir.Record) (χ:Chi){ν:ℕ} (Z:Libretto G ν)
    {U α g :ℝ}{k m:ℕ}(W:Stage)
structure Year (o:ConnectedActivityE6.Target.Order G U) (α t ε:ℝ)(k:ℕ)(A: ConnectedActivityE6.Target G J)(Lc:Side): Prop where
 stays : ∀ (c d:Side)(S':StepData c d)(T':Tube G S'), Works J Lc t S' T' → ∀ (R:RG.Rep G d)(μ c':ℝ)(H:Cash U t μ Lc A o c' T' R) (B:BudgetPoint), B.B=radiusB t→ B.power=W.power→ Plays Z M B R.p J T' t→ A.halo+5≤k→ Release.accepts k R.p.supportExponent ε Lc→ Release.Quotation Z W.power k R.p.supportExponent ε α → Lute.Plented Z M B R.p Lc k t (gStep R.beta)→ ∀ j≥ν, ∀ (C' d h Y A b r B₀ q : ℝ) (l : ℕ), Captain H j C' d h Y A b r B₀ q l Chi.canonical → ∀ q κ', ∀ (X:Set ℕ) (c δ:ℝ), Filed R.p R.activities X c δ→ 0≤δ→δ≤ incomingE G Lc t → Homes X H M q χ Chi.canonical κ' B ε (α / (Lc.val:ℝ)*δ) ((betaF G t Lc) ^ (-(1/80:ℝ))*δ)
theorem spring (hG:G.Simple)(hε:M.ε ≤ 1/4)(o:ConnectedActivityE6.Target.Order G U) (hk:2≤ν)  (v:ℝ)(he: 0≤ v) : ∀ᶠ x in atTop, Year M χ Z W o α x v k A Lc:= by
 by_cases h:∃ D:Patch,D.L=Lc ∧ D.J=J.j ∧ D.Branches J.bind G; swap; · exact Eventually.of_forall fun t=> ⟨fun c f S T h' => (h ⟨S.patch,h'.length_eq,h'.funds.atStep,h'.funds.kernel⟩).elim⟩
 obtain ⟨D,h,hD,hF⟩:= h
 obtain ⟨p,hv,hx⟩:= selected G hG J Lc D hF W.power ν Z M hε hk Chi.canonical χ U o v k he;
 filter_upwards [hx,hv _ (by norm_num : -(1/2:ℝ)< -(1/80:ℝ))] with i hi ht; refine ⟨fun cX dX Sℓ Tℓ hW R μ c' H B hB hb hp ha hv hr hz j hj C' d hE Y A b r B₀ q l N qξ κ' X c δ hS hd hh=>?_⟩
 obtain ⟨⟨u,hp',hy,H₁⟩,w,H,hH,hL⟩:=hi cX dX Sℓ Tℓ (hW.patch h hD) hW _ _ _ _ H B hB hb hp ha _ hv hr hz j hj A b d Y C' B₀ r hE q _ N qξ κ' X c δ hS hh -- duplicate variables. use renamed.
 exact ⟨⟨u,hp',hy,fun i=> budget_loosen (H₁ i) le_rfl⟩, w,fun i=>budget_loosen (H i) (mul_le_mul_of_nonneg_right ht hd),hH,hL⟩
end crispPaper
end YM.PhysicalNext.Repeat.Brim.WilsonMovingSingleton
end

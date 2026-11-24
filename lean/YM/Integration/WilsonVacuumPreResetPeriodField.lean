import YM.Integration.WilsonVacuumPreResetPeriodEntries
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite

/-! The full supported independent period action as read in the same genuine
reset. At arbitrary compact fields it uses the actual local masks. On the
quiet chamber its rooted total is the original signed finite period action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPeriodField
open Function Finset Lattice RG Wilson Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum Extra.Iteration
open AnalyticBridge VerifiedReset Collection Quotes LocalComparison.Global
open WilsonVacuumPreResetPeriodEntries
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

private theorem rows (B:BudgetPoint)(Z:List (Piece G n))(k:ℕ → ℕ → ℝ)(p:Render.permits Z B)(U:Config G n):
    (tally Z k).Valid B (quote Z k) 0 ∧ (tally Z k).additive B U=Render.renders (fun a=>k a.power a.rank) B U Z:=by
  induction Z with
  | nil=>exact ⟨Pane.whey n G B,(Pane.pale_value B U).1⟩
  | cons a l ih=>
    obtain ⟨h,h'⟩:=ih (Render.seated p)
    have v:=Payload.payment (k a.power a.rank) (Render.first p) h
    have e:=Payload.pays_add (k a.power a.rank) (Render.first p) h U
    refine ⟨?_,?_⟩
    · change (a.packet.attach (k a.power a.rank) (tally l k)).Valid B (‖k a.power a.rank‖*a.credit+quote l k) 0
      rwa [add_comm]
    · change (a.packet.attach (k a.power a.rank) (tally l k)).additive B U=_
      rw [e,h',add_comm]
      rfl

theorem maskedRows (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent B / B.B ≤ σ/4)(blocks:2 ≤ B.B)
    (Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ → ℕ → ℝ)(U:Config G n):
    (entries n B σ C Z k).additive B U=Render.renders (fun a=>k a.power a.rank) B U
      (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)):=by
  have permit:=FundedCorrectedPeriod.permits Z draw simple hn (Song.headline B) hs reach blocks
    (Pane.pale n G) (fun s b=>((Pane.whey n G (Song.headline B)).moves s b).some)
  rw [same (n:=n) B (Song.headline B) σ C Z k]
  let L:=Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)
  calc
    _=(tally L k).additive (Song.headline B) U:=rfl
    _=Render.renders (fun a=>k a.power a.rank) (Song.headline B) U L:=(rows _ L k permit U).2
    _=Render.renders (fun a=>k a.power a.rank) B U L:=by
      suffices ∀ L:List (Piece G n),Render.renders (fun a=>k a.power a.rank) (Song.headline B) U L=
          Render.renders (fun a=>k a.power a.rank) B U L from this L
      intro l
      induction l with
      | nil=>rfl
      | cons a l ih=>simp only [Render.renders,ih]; rfl

private theorem quietList (B:BudgetPoint)(Z:List (Piece G n))(k c:ℝ)(U:Config G n)(quiet:flags B.threshold U=∅):
    Render.renders (fun a=>k*c^(a.power+2-a.rank)) B U Z=k*ActualGradedVacuum.restored Z c U:=by
  induction Z with
  | nil=>simp [Render.renders,ActualGradedVacuum.restored]
  | cons a l ih=>
    have amt:a.packet.amount B U=unmaskedPayload a.packet U:=by
      apply tsum_congr
      intro i
      have clean:Healthy B.threshold (a.packet.labels i).support U:=by simp [Healthy,quiet]
      simp [masked,clean]
    change k*c^(a.power+2-a.rank)*a.packet.amount B U+Render.renders _ _ _ l=k*(_+_)
    rw [ih,amt,mul_add,mul_assoc]
    rfl

theorem rooted (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent B / B.B ≤ σ/4)(blocks:2 ≤ B.B)
    (Z:SeriesA G)(draw:Draw Z σ C)(grade:∀a∈Z,0<a.grade)(k c:ℝ)(U:Config G n)(quiet:flags B.threshold U=∅):
    (entries n B σ C Z (fun d r=>k*c^(d+2-r))).additive B U =
      ∑ x:Site n,k*OriginalMarkedRunAction.springPacketsAt Z c x U:=by
  rw [maskedRows simple hn B hs reach blocks Z draw,quietList B _ k c U quiet,
    FundedCorrectedPeriod.restored Z draw grade hs (Song.headline B) c U,
    OriginalMarkedRunAction.period_sites,Finset.mul_sum]

end YM.Integration.WilsonVacuumPreResetPeriodField

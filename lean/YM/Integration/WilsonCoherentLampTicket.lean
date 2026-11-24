import YM.Integration.WilsonCoherentFiniteIssue

/-! The entire enrolled finite stencil is a specific FVA2 ticket. Its inlet
eigen-grade is removed only after the original normalized joint Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentLampTicket
open Filter Function PowerSeries Lattice Wilson RG Tree Precision
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router
open RGComparison.Core16 RGComparison.Core16.Lumen FVA2 FVA2.CityHistory FVA2.RayScatter
open scoped Topology ContDiff

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Spool.Lamp G)
variable {c f : Side} (S : StepData c f) (T : Forest S.ratio) (o : I → Site f) (part : Bool)

def source (z : Future G S T × Pins G c) : ℝ :=
  Spool.look part (Spool.sight J (Fk.scene (Spool.earns S T J o) (0,z.1)))

/-- Every absent tree edge is the original zero letter. The entered mark
therefore has identical values on the true radial reading and on the
joint held/free ticket, for every choice of the hold. -/
theorem entered (u : Pins G c) (w : Fk.Door G T.Free) :
    (Spool.look part ∘ Spool.sight J) (Fk.scene (Spool.earns S T J o) w) =
      source J S T o part (recover u w) := by
  have eq : Fk.scene (Spool.earns S T J o) w = Fk.scene (Spool.earns S T J o) (0,w.2) := by
    funext a
    simp only [Fk.scene,Spool.earns]
    split <;> simp
  exact congrArg (Spool.look part ∘ Spool.sight J) eq

theorem admitted : ContDiffAt ℝ ω (source J S T o part) 0 := by
  let E := Future G S T × Pins G c
  let v := Spool.earns S T J o
  have coords : ContDiffAt ℝ ω (Fk.scene v) 0 := by
    apply contDiffAt_pi.mpr
    intro k
    unfold Fk.scene
    rcases v k with l | a
    · exact turn_hot.contDiffAt.comp (f:=fun x:Fk.Door G T.Free => x.2 l) _
        ((contDiff_apply ℝ _ _).contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd)
    · exact contDiffAt_fst.smul contDiffAt_const
  have origin : Fk.scene v (0:Fk.Door G T.Free)=0 := by
    funext a
    unfold Fk.scene
    cases v a <;> simp [Fk.spread,comp_apply]
  have analytic := ((origin.symm ▸ Spool.sphere J part :
    ContDiffAt ℝ ω (Spool.look part ∘ Spool.sight J) (Fk.scene v (0:Fk.Door G T.Free)))).comp _ coords
  let wire : E → Fk.Door G T.Free := fun z => (0,z.1)
  have wire_hot : ContDiffAt ℝ ω wire (0:E) := contDiffAt_const.prodMk contDiffAt_fst
  have at_zero : wire (0:E)=0 := rfl
  exact ((at_zero.symm ▸ analytic : ContDiffAt ℝ ω _ (wire (0:E)))).comp (0:E) wire_hot

theorem booked {P : Parcel.Oven S.patch} (X : P.Form G) (Z : ChartRatio G) (ratio : LocalRatio Z)
    (large : Bid.Larger (G:=G) S) (u : Pins G c) (paid : P.Offers X S.kernel)
    (inside : ∀a,‖u a‖≤X.Q) (b : S.Choices) (v : (Descent.nil (top:=f)).Tags) :
    PowerSeries.mk (Spool.rankℝ J S T X Z u o part) =
      Stack.drop (Spool.power J) (Stack.read u
        (solenoid S T Descent.nil v b Z 1 large (show (Descent.nil (top:=f)).Room G from trivial)
          (Stack.rise (source J S T o part)))) := by
  let Q:=gateQ S T b (retained Descent.nil v (show (Descent.nil (top:=f)).Room G from trivial))
  have hQ:= useful S T Descent.nil v b large (show (Descent.nil (top:=f)).Room G from trivial)
  have row := Fork.perch (Spool.lens (S:=S) u X T) Z ratio (Spot.thermalHeat S T b large)
    Q (Spot.precisionHeat S T b large v) hQ u (ψ:=Spool.look part ∘ Spool.sight J) (Spool.earns S T J o)
    (Spot.prospect S T b u large P X paid inside) (source J S T o part)
    (Eventually.of_forall (entered J S T o part u)) (admitted J S T o part) (Spool.power J)
  simpa only [solenoid,Pi.one_apply,Spot.fusionL S T Z b large v,Spool.rankℝ,Q,hQ] using row

end YM.Integration.WilsonCoherentLampTicket
end

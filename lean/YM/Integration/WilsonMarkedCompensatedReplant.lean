import YM.Integration.WilsonMarkedRegulatorHistory

/-! A complete ordinary selected word can be restarted as one signed source.
The full ordinary table is formed prior to its linear capture and subtraction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedCompensatedReplant
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FormalBulk08 Sierra Pose Stationary
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Winding
open WilsonPointChildScalarSlot (grade roster outlet inlet)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{h k:ι→ℕ}

def capture (M:Outerm G h)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ)(positions:Cover→ι→ Cover)
    (C:Cover→ Era G ℝ):Outerm G grade:=fun z=>roster (tuftV f (levelsO (M (positions (z ()))) S)-C (z ()))

/-- All field-independent but marked terms survive on the located occupied
coordinate. Each originally selected position is used before capture. -/
theorem exact_seed (M:Outerm G h)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ)(positions:Cover→ι→ Cover)
    (C:Cover→ Era G ℝ)(z:Unit→ Cover):
    tuftV outlet (capture M S f positions C z {()})=tuftV f (levelsO (M (positions (z ()))) S)-C (z ()):=by
  rw [capture,WilsonPointChildScalarSlot.full]
  apply Prod.ext
  · funext n e r x;exact WilsonPointChildScalarSlot.submitted _
  · funext e r x;exact WilsonPointChildScalarSlot.submitted _

theorem intake (M:Outerm G h)(income:Wellness k M)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ)
    (positions:Cover→ι→ Cover)(C:Cover→ Era G ℝ)(counter:∀x,Auth (mass k S) (C x)):
    Wellness (fun _:Unit=>mass k S) (capture M S f positions C):=by
  refine ⟨fun z=>WilsonPointChildScalarSlot.empty _,fun z=>WilsonPointChildScalarSlot.legal
    (((placedO _ (income.level' _) S).tuft f).sub (counter _)),?_⟩
  intro p q J same
  by_cases hit:J={()}
  · subst J;rw [capture,capture,same () (Finset.mem_singleton_self ())]
  · simp only [capture,WilsonPointChildScalarSlot.roster,dif_neg hit]

/-- On the original prescription, the actual numerical restart has just one
external name from capture to its older filing. Its angular coordinates carry
the complete ordinary input less the nominated same-date field. -/
theorem original (R:Run G)(simple:G.Simple)(o:Loc G 1)(N b j:ℕ)(born:b≤N)(age:j≤b)
    (M:Outerm G h)(income:Wellness k M)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ)(positions:Cover→ι→ Cover)
    (C:Cover→ Era G ℝ)(counter:∀x,Auth (mass k S) (C x))(engineering:ℕ)(z:Unit→ Cover):
    let H:=Gears R.family.path.levels R.metals.O (fun _:Unit=>engineering) (fun _:Unit=>mass k S)
      N b j (capture M S f positions C) z
    WilsonMarkedRegulatorHistory.Warps (mass k S) (tuftV outlet (H {()})):=by
  intro H
  have got:=WilsonMarkedRegulatorHistory.original R simple o (fun _:Unit=>engineering) _
    (intake M income S f positions C counter) N b j born age z {()} outlet
  simpa only [H,mass,Finset.sum_singleton] using got.1

end YM.Integration.WilsonMarkedCompensatedReplant
end

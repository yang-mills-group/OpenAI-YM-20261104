import YM.Integration.WilsonNeutralAppointedForestStep
import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! Read the unreset normalized filed column on the actual cofinal filter of
the receiving Wilson Post. The observing side may itself be a multiple of
the physical period. The count and residue map are those of its literal
copied-color construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralReceivedCoverLimit
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical

def multiplicity (S:Schedule) (i:ℕ) (n:Side) (b:Covers S i n) : Side :=
  ⟨(S.side i b.val).val/n.val,Nat.div_pos (Nat.le_of_dvd (S.side i b.val).pos b.prop) n.pos⟩

theorem actual_size (S:Schedule) (i:ℕ) (n:Side) (b:Covers S i n) :
    multiplicity S i n b*n=S.side i b.val := Subtype.ext (Nat.div_mul_cancel b.prop)

theorem growing (S:Schedule) (i:ℕ) (n:Side) :
    Tendsto (multiplicity S i n) (coverFilter S i n) atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [(cover_size S i n).eventually_ge_atTop (k.val*n.val)] with b hb
  exact (Nat.le_div_iff_mul_le n.pos).2 hb

theorem copies (S:Schedule) (i:ℕ) (n:Side) (b:Covers S i n) :
    Pages n (S.side i b.val)=(multiplicity S i n b).val^4 := rfl

theorem residues (m n:Side) (x:Site (m*n)) : (Shore.endo m n).residue x=
    (coverWin (n:=n) (N:=m*n) (dvd_mul_left n.val m.val)).cut x := by
  obtain ⟨z,rfl⟩:∃z:Cover,x=wrap (m*n) z:=⟨_,(wrap_lift _).symm⟩
  rw [coverWin_cut, branch, Ratio.residue_wrap]
  rfl

variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

include grant in
theorem original (N i:ℕ) (hs:G.Simple) (o:Loc G 1) (live:i<N)
    (hd:d≤R.family.path.levels.clock.J (i+1)) (n:Side)
    (F:∀n:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).ratio)
    (t:∀n:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b:Letter (R.family.labels.level d)) (f:Studio D) (e r:ℕ) (v:chain (wire G n) r) :
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let y:=Primer.fieldCoeffs R.family a wood depth N (i+1)
    let pre:=Kemp.quick A (wood i) w (y b) R.metals.O (R.family.path.levels.blocks i 0).branches
      (Elm.growL R.family.path.levels i) d d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>
      let m:=multiplicity R.family.path.levels.S i n c
      Shore.cores (Shore.tray m n)
        (rancho (WilsonNeutralAppointedForestStep.integral R wood a depth N i (m*n) (F _) (t _) b f) e r) v)
      (coverFilter R.family.path.levels.S i n) (𝓝 (rancho (Kemp.banner d (pre f) n) e r v)) := by
  intro A w y pre
  have c:=WilsonRunFormalMarkedStep.normalized R wood a depth hs o N (i+1) live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have path:Wade o (y b) (slots (R.family.labels.level d) b):=by
    simpa only [y,←WilsonNeutralAppointedForestStep.column R wood a depth grant] using (c.officers b).fare
  have story:Story w (pink R.family.path.levels.clock.kernel.penalty A.wing):=by
    dsimp only [w]
    rw [←WilsonNeutralAppointedForestStep.vacuum R wood a grant]
    exact (Dove.genu R.family.path.levels wood (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a R.alloy.B.ratio hs (i:=i+1) (N:=N) live).toStory
  have fit:=slotsFits (R.family.labels.level d) b
  have admitted:Wade o pre d:=(Kemp.quick_Wade o A (wood i) (y b) w R.metals.O (R.family.path.levels.blocks i 0).branches
    path story R.alloy.B.ratio (Elm.growL R.family.path.levels i) (R.family.path.levels.clock.adm i) fit d).through fit
  obtain ⟨η,η0,estimates,-⟩:=Kemp.brig o A (wood i) (y b) w R.metals.O (R.family.path.levels.blocks i 0).branches
    path story R.alloy.B.ratio (Elm.growL R.family.path.levels i) (R.family.path.levels.clock.adm i) fit t e r d
  rw [Kemp.badge (pre f) (admitted.1 f) (admitted.2.1 f) le_rfl]
  refine ((Kemp.sieve_copy n (estimates f) η0 v).comp (growing R.family.path.levels.S i n)).congr'
    (.of_forall fun j=>?_ )
  dsimp only [Function.comp_def]
  rw [Kemp.preQ o A (wood i) w R.metals.O (R.family.path.levels.blocks i 0).branches path
    (Elm.growL R.family.path.levels i) fit t f d]
  rw [←WilsonNeutralAppointedForestStep.input R wood a depth grant N i hs o live hd]
  rw [WilsonNeutralNormalizedForestStep.received R wood a depth N i hs o live hd _ (F _) (t _) (t _) b f]
  dsimp only [w,y,A]
  rw [←WilsonNeutralAppointedForestStep.column R wood a depth grant,←WilsonNeutralAppointedForestStep.vacuum R wood a grant]
  rfl

end YM.Integration.WilsonNeutralReceivedCoverLimit
end

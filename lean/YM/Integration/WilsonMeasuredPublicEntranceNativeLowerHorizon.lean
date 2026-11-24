import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerInduction
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRestriction
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerHorizon
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open WilsonMeasuredPublicEntranceBranchGap (watches)
theorem original {F:Final C f S}{J:ℝ→tower S}(lead:Leading F J){A:Type*}{l:Filter A}[NeBot l]
    {r t:A→ℝ}{s:ℝ}(near:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hs:0<s)(pos:∀i,0<t i)
    {k:ℕ}(top:Module.End ℂ (D k))(heard:∀v,Tendsto (fun i=>Frame.cocycle k J (r i) (t i) (pos i) v) l (𝓝 (top v)))
    (cells:∀d,d≤k→∀Z:Module.End ℂ (D d),
      (∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))→
      ∃price:WilsonMeasuredPublicEntranceBranchGap.Axis C d→ℝ,(∀j,0≤price j) ∧
        ∀i j,watches C i j→let B:=Extra.FD.recorded C.labels d
          (B.w j).1=d→B.b.coord i (Z (B.b j)-(price j:ℂ) • B.b j)=0):top=1:=by
  have far:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero] using ht.mul (near.mono_right nhdsWithin_le_nhds)
    filter_upwards [near.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
  obtain ⟨Z,same,filed,connected⟩:=WilsonMeasuredPublicEntranceNativeLowerRestriction.original lead near far pos top heard
  have grades d hd:=WilsonMeasuredPublicEntranceBranchGap.income F J lead near hs ht pos (Z d hd) (filed d hd)
  have pay d hd:=cells d hd (Z d hd) (filed d hd)
  let price d hd:=(pay d hd).choose
  have fixed:=WilsonMeasuredPublicEntranceNativeLowerInduction.original Z (fun d hd=>(grades d hd).1)
    (fun d hd=>(grades d hd).2) connected price (fun d hd=>(pay d hd).choose_spec.1) (fun d hd=>(pay d hd).choose_spec.2)
  exact same.symm.trans (fixed k le_rfl)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerHorizon
end

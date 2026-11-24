import YM.Integration.WilsonOriginalPublicNodalOrbitStride

/-! Both independent stopped banks return to the original sites from one safe translate of the whole group. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTwinOrbit
open Lattice RG Source Labels PertExtension XSpace XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Motion
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalSafeCenter (moved)
open WilsonOriginalPublicNodalCommonRaw (Court value fee prior raw Offered)
open WilsonOriginalPublicNodalOrbitStride (blocks actual)
open WilsonOriginalPublicNodalSafeCopies (safe shift)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{I X:Type}{p:ℕ}
def stride (A B:Court G X p)(j:Choice A.M)(k:Choice B.M)(w:X):ℕ:=
  Nat.lcm (blocks A.V (j.choose w)) (blocks B.V (k.choose w))

def lift (P:X → ℝ)(s:X → ℕ)(base:X → Cover)(sites:X → I → Cover)(w:X)(i:I):Cover:=
  sites w i+s w • shift (P w) (s w) (base w)

theorem original (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)(A B:Court G X p)(samples:X → Sample 2)
    (base:X → Cover)(sites:X → I → Cover)(j:Choice A.M)(k:Choice B.M)(earA:A.D.age ≤ j.age)(earB:B.D.age ≤ k.age)
    (q:ℕ)(hq:q≤p)(topA:∀w,TopF A.n w=(samples w).F.p.side)(topB:∀w,TopF B.n w=(samples w).F.p.side)
    (same:∀w,A.S.P w=B.S.P w)(room:∀w,(stride A B j k w:ℝ) ≤ A.S.P w/8)
    (fundA:∀w,ENNReal.ofReal (1+span (slide 1 (base w)) (sites w) arms) ≤ A.L.val w)
    (fundB:∀w,ENNReal.ofReal (1+span (slide 1 (base w)) (sites w) arms) ≤ B.L.val w):
    ∃U V H:ℝ,∃u v h:ℕ,0≤U ∧ 0≤V ∧ 0≤H ∧ ∀n:Page k.after.spans,
      let w:=n.bindW
      let z:=lift A.S.P (stride A B j k) base sites
      let a₀:=value R W σ d key arms A sites (j.choose w) q
      let b₀:=value R W σ d key arms B sites (k.after.page n) q
      ‖a₀-raw R W σ d key arms (samples w) (z w) q‖ ≤ fee A U u j w ∧
      ‖raw R W σ d key arms (samples w) (z w) q-b₀‖ ≤ fee B V v k w+prior B H h k w ∧
      ‖a₀-b₀‖ ≤ fee A U u j w+(fee B V v k w+prior B H h k w):=by
  let s:=stride A B j k
  let c:=fun w=>safe (A.S.P w) (s w) (base w)
  let z:=lift A.S.P s base sites
  have pos (w:X):0<s w:=Nat.lcm_pos (WilsonOriginalPublicNodalOrbitStride.positive A.V _)
    (WilsonOriginalPublicNodalOrbitStride.positive B.V _)
  have shifted (w:X):span (slide 1 (c w)) (z w) arms=span (slide 1 (base w)) (sites w) arms:=by
    change span (slide 1 (base w+s w • shift _ _ _)) _ _=_
    rw [map_add]
    exact WilsonOriginalPublicNodalSafeCenter.geometry arms _ _ _
  have clear (w:X): (1/8:ℝ)*A.S.P w≤Spatial.singular (A.S.P w) (slide 1 (c w)):=
    WilsonOriginalPublicNodalSafeCopies.cushion _ _ _ (pos w) (room w)
  have left:Offered arms A samples z (fun w=>slide 1 (c w)) (1/8):=
    ⟨topA,fun w=>by rw [shifted];exact fundA w,by norm_num,clear⟩
  have right:Offered arms B samples z (fun w=>slide 1 (c w)) (1/8):=
    ⟨topB,fun w=>by rw [shifted];exact fundB w,by norm_num,fun w=>by rw [←same];exact clear w⟩
  choose a b ha hb using fun w=>WilsonOriginalPublicNodalSafeCopies.common (A.S.P w) (s w) (base w)
    (blocks A.V (j.choose w)) (blocks B.V (k.choose w)) (Nat.dvd_lcm_left ..) (Nat.dvd_lcm_right ..)
  have placed (T:Court G X p)(e:Choice T.M)(t:X → Cover)
      (ht:∀w,c w=base w+blocks T.V (e.choose w) • t w):moved T.V e (fun w=> -t w) z=sites:=by
    funext w i
    have eq:=add_left_cancel (ht w)
    change sites w i+s w • shift _ _ _+_ = sites w i
    rw [actual,smul_neg,←eq,add_neg_cancel_right]
  have az:=placed A j a ha
  have bz:=placed B k b hb
  obtain ⟨U,V,H,u,v,h,hU,hV,hH,ret⟩:=WilsonOriginalPublicNodalCommonRaw.intersection
    R W σ d key arms A B samples z (fun w=>slide 1 (c w)) (1/8) (1/8) left right j k earA earB
    (fun w=> -a w) (fun w=> -b w) q hq
  refine ⟨U,V,H,u,v,h,hU,hV,hH,?_⟩
  intro n
  simpa only [az,bz,add_assoc] using ret n
end YM.Integration.WilsonOriginalPublicNodalTwinOrbit
end

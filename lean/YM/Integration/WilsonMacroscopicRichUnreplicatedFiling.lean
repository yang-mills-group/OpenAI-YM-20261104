import YM.Integration.WilsonMacroscopicRichRetainedCaptureComparison

/-! A common physical terminal filing from one full signed coefficient at capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichUnreplicatedFiling
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open MergeProof MergeProof.Accent MergeProof.Float PhysicalNext.Repeat Lotus RG16.Literal
open Extra.Histories.Relay Trace.Physical.GermGraph Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} (C:Family G) (N k m p d:ℕ) (H:C.Makes)
variable {W:Worth} {u ψ φ δ:ℕ → ℝ} {r:ℕ → ℕ} {ζ:ℕ → ℕ → ℝ}
  {D:∀ N p i:ℕ,i<N → GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
local notation "T"=>C.path
local notation "R"=>C.path.rep N p
local notation "S!"=>C.localSection d
local notation "F"=>C.labels.level d
local notation "T!"=>C.factory d N p

theorem original (scrim:Scrim C W u ψ φ δ ζ r D) (w:ℝ) (wpos:0 < w)
    (f:Cut C N p) (hf:Continuous f) (Q:Coefficient F (C.side k p)) (t c E:ℝ)
    (ht:C.ref d ≤ m)(mk:m ≤ k)(kN:k ≤ N)
    (formatted:Q.Format 0 C.params (R k))
    (forced:Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t)
    (amount:(F).coeffSize Q.x+t ≤ c)(cpos:0 < c)
    (headroom:4*(1+(C.path.levels.params k).columns)*c ≤ E)
    (reserve:w*‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2)
    (source:credit C N p d f k kN=Q.density 0 S! (R k)) :
    ∃ z:C.label d, Next.UVStress.quota C d k N p z ≤ 2*E ∧
    ∃ (Z:∀ i,Coefficient F (C.side i p)) (g:ℕ → ℝ),
      Club T C.params S! (ζ d) ψ m k N p (fun i=>march (fun _:Unit=>w) φ m i ()) D Z g kN ∧
      (∀ i,m ≤ i → i ≤ k →  g i+(F).coeffSize (Z i).x ≤ E/gainChart T k i) ∧
      (Z k).exponentialEntry 0 S! (R k)=Q.exponentialEntry 0 S! (R k)+
        ((T!).entries k (-(T!).terminal.symm z)).exponentialEntry 0 S! (R k) ∧
      profile (R k).activities (Z k).forced = profile (R k).activities Q.forced+
        profile (R k).activities ((T!).entries k (-(T!).terminal.symm z)).forced ∧
      (Z k).density 0 S! (R k)=credit C N p d f k kN+
        ((T!).entries k (-(T!).terminal.symm z)).density 0 S! (R k) ∧
      ∀ (i:ℕ),m ≤ i → ∀ (ik:i ≤ k)(door:Opened C d i p),
        mCost C d N p i (topReport C N p d H i door (ik.trans kN) f-(T!).terminal.symm z)
           ≤ E/gainChart T k i := by
  obtain ⟨X,hX,hL,hY,_⟩:=(scrim.costs.aim d N p (ht.trans (mk.trans kN))).lyrics
  obtain ⟨Z,g,v,club,cap,exp,gas,density,budget⟩ :=
    retains_cancellation C N k m p d H w X scrim Q t c E ht mk kN hL hY
      formatted forced amount headroom cpos wpos reserve
  let z:=(T!).terminal v
  have re:(T!).terminal.symm z=v:=LinearEquiv.symm_apply_apply ..
  have file:(T!).entries=(X.draft T).inits:=hX
  have bill:Next.UVStress.quota C d k N p z ≤ 2*E := by
    unfold Next.UVStress.quota
    rw [re,file,show ((X.draft T).inits k v).x=_ from (hL.earned k (ht.trans mk) kN).currents v]
    exact cap
  have matchAt:(T!).entries k (-(T!).terminal.symm z)=(X.tone k).plays (-v):=by rw [re,file];rfl
  have charge:(Z k).density 0 S! (R k)=credit C N p d f k kN+
      ((T!).entries k (-(T!).terminal.symm z)).density 0 S! (R k):=by rw [matchAt,source];exact density
  refine ⟨z,bill,Z,g,club,budget,?_,?_,charge,?_⟩
  · rw [matchAt];exact exp
  · rw [matchAt];exact gas
  · exact WilsonMacroscopicRichCommonFiling.readings (C:=C) (N:=N) (p:=p) (d:=d) (b:=k) (u:=m)
      (X:=Z) (h:=H) (hN:=kN) (hh:=club) (f:=f) (hf:=hf) (z:=z) (hR:=charge) budget

end YM.Integration.WilsonMacroscopicRichUnreplicatedFiling

import YM.OPE.Script.Wagon
/-!
# Quantitative estimates for ANY live packet at origin that's received
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{C:Family G}{N k m p d j:ℕ}
variable {W:Worth}{b :ℕ} {u ψ φ δ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
open Relay GridApprox
local notation "T"=> C.path
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "R"=> C.path.rep N p
local notation "V"=> Site (C.side j p)
local notation "Z"=> (R k)
local notation "f"=> C.side N p
variable {Y₁:I→ Config G (C.side N p)→ℂ} {o:I→Site (C.side k p)}{d₀:Finset I}{P:I→Lamp G (C.side k p)} {w:I→ℝ}{e t c a E:ℝ}
    {hk:j≤k}{Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side j p)) I)}
    {Q':Coefficient (C.labels.level d) (C.side k p)} {B:Album C N k p d}
namespace Wagon
-- Restrict at master entry
lemma capture (H:C.Makes)(h:Scrim C W u ψ φ δ ζ r D)(hn:k<N)(hp:Wagon C N p j k hk hn.le Q Y₁ d₀ o P w) (hz:Stock.Tabs C.path.levels) (he:Stock.Tabs.opens C.path.levels 1 j m) (ht:C.ref d ≤ m)(hN:m < k) (hR:GridApprox.room C.path.levels j k (lensScope C d))
    (hC:∀ b:C.label d,Interior ((center C.S p (hk.trans hn.le) 0).chamber 0) (C.O N p b 0)) (i:I)(hX:o i=0) (hf: Interior ((center C.S p (hk.trans hn.le) 0).chamber 0) (Y₁ i)) (hB:Chant W D ζ ψ φ Q' E B hn.le)
    (hx: Ignite T N p k C.params Y! Q' c 0 (P i))(hE:0<E)(ha:0<a)(hP:32*(1+(T|>.levels.params k).columns)*a * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2) (hw:stair φ a m k ≤ w i) : Next.UVStress.quota C d k N p B.legacy ≤ 2*E∧ (center C.S p (hk.trans hn.le) 0).rootTest (C.beta N p) (Y₁ i-C.O N p B.legacy 0) ≤ 2*(stakes C j m / a):=by
    let L:Extra.Trajectories.Names (Stock.census V) (Names V I):=⟨⟨fun v=>(v,i),fun _ _ h=>congr_arg Prod.fst h⟩, fun _=>mem_univ _⟩
    let S₀:= royal C j p k; let t':=Mix.camp C p j k; let r':=stair φ a m k; let B':= hands C p j; let U':= Q'.exponentialEntry 0 (C.localSection d) Z; let Q₁:= L.restriction ∘ Q
    refine hB.request (hk:=hN.le) H h j he _ Q₁ hz ht hn hN hR hC ?_ hf hE ha hP ?_ -- args order?
    · refine (Eq.mp ?_ (hp.script.corps L)); congr 1; ext1 v; exact callsR (hk.trans hn.le) Y₁ (v,i)
    have hS:= hp.fleet.sem.sold.read L (fun j=>hp.fleet.secure j.2); have ho' : S₀.place o ∘ L.e=t':=by funext v; change S₀.place o (v,i)= _; rw [placeR hk, hX]; simp [t',affine]
    have hY: S₀.lamp P ∘ L.e=(fun j=> radiant (alto T k d) (B' j) (t' j) U'):=by
       let y:=alto T k d; funext j; change Brigade.calls S₀ (fun i=>(P i).watch) (j,i)= _; unfold Brigade.calls; dsimp only; rw [hx.track]; split; next ht=> have h': j=0:= ht; subst j; unfold B' t'; rw [h',P_on,zeroMama C _ p _ hk]
       unfold radiant; rw [stepid]; funext U; simp only [stepUp,Pi.smul_apply,smul_eq_mul,lept]; rfl
    have hf': S₀.ray (R k) P ∘ L.e=(fun j=> sunny (R k) Q'.forced (B' j) (t' j) (alto T k d)):=by
       funext j; change S₀.ray (R k) P (j,i)=_; unfold Brigade.ray; rw [hx.rays]; split; next ht=> have h': j=0:= ht; subst j; unfold B' t'; rw [P_on,zeroMama C _ p _ hk]
       unfold sunny; rw [floatid]; funext b u; simp_rw [floatUp,stepUp,Pi.smul_apply,smul_eq_mul,lept]; rfl
    -- normalize march
    let t:V→ℝ:= march (fun _:V=>a) φ m k; have hW : t=fun _=>r':=by
       funext i; suffices h:∀ j:ℕ,march (fun _:V=>a) φ m j i=march (fun _:Unit=>a) φ m j () by exact h k
       intro j; induction j with
       | zero=> rfl
       | succ j hj=> by_cases h:m ≤ j <;> simp [march,h,hj]
    have hw': Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have hR':0<r':= march_pos _ _ _ _ _ (fun _=>ha) hw' k hN.le _
    rw [← (H.wilson.represents N p k hn.le).vac]; rw [hY,hf',ho', show ((w ∘ Prod.snd) ∘ L.e)=(fun _:V=>w i) from rfl] at hS
    rw [show march (fun _ : V=> a) φ m k= _ from hW]; exact hS.prune (fun _=> hp.fleet.secure _) (fun _=>hR') (slighter (fun _=>hp.fleet.secure _) (fun _=>hR') (fun _=>hw.trans_eq ((one_mul _).symm)) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num)
end Wagon
end YM.MergeProof.Ribbons.ManyCopies.Patrol

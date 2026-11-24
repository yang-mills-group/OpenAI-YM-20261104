import YM.FormalOPE.RG10.Carryon.Slip
/-! Leading hypothesis for position-rank only needed on finite diagnostic tests. Then exact
uniqueness under the frame calls. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{d k:ℕ}
local notation "Κ" d=> Matrix (Deck F d) (Deck F d) fps
local notation "Λ" d=> Matrix (Deck F d) (Deck F d) ℝ
local notation "T"=>PertExtension.Physical.Profile.n
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "ins" => PertExtension.Position.insert (Deck F d) T
local notation "Diag"=> Physical.diag

variable (D:Stock F)(u:(Mark (Deck F d) PertExtension.Physical.Profile.n)→fps)
abbrev probe (v:Mark (Deck F d) PertExtension.Physical.Profile.n→fps) : (D d).Parameter:= fun i=> constantCoeff (v (markIn (D d).tests i))
abbrev crib := (D d).leadingAdjust (raw F d) (fun v=>constantCoeff (u v))
abbrev posture : Κ d:= of ((crib D u).position u)
def respects (A:Κ d) := ∀ i,(D d).response u A i= if i=0 then (D d).target else 0
def Credible := (crib D u).Regular (fun v=> constantCoeff (u v))

-- Leading authority. Only requires those tests.
variable {D} (h: Official D)
local notation "ℳ" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
include h
lemma agree : (D d).Z = tents F d:= Submodule.ext (fun A=> (h.tangent ..).trans (pinned A).symm)
local notation "E"=> D d
lemma installed : Upright (posture D u):= by
 apply Upright.obtainable
 · rw [diag_one,← agree h]; let t:= (E).branch (raw F d) (probe D u)
   have he : Stg (posture D u) 0 = of (Diag (Deck F d))+ of t.val := by ext i j; simp [Stg,posture,crib,TestSystem.leadingAdjust,h.normal]; rfl
   rw [he]; change Diag (Deck F d)+ t.val - Diag (Deck F d) ∈ (E).Z; rw [add_sub_cancel_left]; exact t.property
 intro i hi; rw [← agree h]; exact (crib D u).positive_variation u i hi.ne'

variable {I:Type*}{l:Filter I}
abbrev listens (b: I→ (Mark (Deck F d) PertExtension.Physical.Profile.n)→fps):= Tendsto (fun i=>probe D (b i)) l (𝓝 (raw F d ∘ markIn (D d).tests))
-- not depend h
omit h in
private lemma certifiedBind (v w: Mark (Deck F d) PertExtension.Physical.Profile.n→ℝ) (U: TestSystem (Deck F d) PertExtension.Physical.Profile T)(he: v ∘ markIn U.tests=w ∘ markIn U.tests)(hh:U.Regular v) : U.Regular w:= by
 obtain ⟨v',u⟩:=hh; rw [he] at v'; unfold TestSystem.inspect at u; rw [he] at u; exact ⟨v',u⟩

lemma credential (b: I→(Mark (Deck F d) PertExtension.Physical.Profile.n)→fps) (k:listens (l:=l) (D:=D) b) : ∀ᶠ i in l, Credible D (b i):= by
 let g : (V d)→ ℝ:=raw F d
 let L:= E
 let a(i) (p:V d):= if p∈Set.range (markIn (J:=Deck F d) (arity:=T) (E).tests) then constantCoeff (b i p) else raw F d p
 have hev i j : a i (markIn (E).tests j) = probe D (b i) j:= if_pos ⟨j,rfl⟩
 have ha : ∀ z, AlignSeries l (fun i=> PowerSeries.C (a i z)) (C (g z)) := by
   intro v; apply AlignSeries.scalar_C; by_cases h:v∈Set.range (markIn (E).tests);
   · obtain ⟨j,rfl⟩:=h; simp_rw [hev]; exact (tendsto_pi_nhds.1 k) j
   unfold a; simp_rw [if_neg h]; exact tendsto_const_nhds
 have hg:L.Regular g:= h.fresh d
 filter_upwards [L.leading_achieved (PowerSeries.C ∘ g) (fun i=>PowerSeries.C ∘ a i) (by simpa only [Function.comp_apply,constantCoeff_C] using hg) ha] with i hi;
 unfold TestSystem.systemAt at hi; change (L.leadingAdjust (fun i=>constantCoeff (C (g i))) (fun v=>constantCoeff ((⇑C ∘ a i) v))).Regular (fun j=>constantCoeff ((⇑C ∘ a i) j)) at hi; simp only [Function.comp_apply,constantCoeff_C] at hi
 have hv : a i ∘ markIn (D d).tests = (constantCoeff ∘ b i) ∘ markIn (D d).tests:= funext (hev i)
 have hx : L.leadingAdjust g (a i)=crib D (b i):= by unfold TestSystem.leadingAdjust; rw [hv]; rfl
 rw [hx] at hi; exact certifiedBind _ _ (crib D (b i)) hv hi -- args

lemma start_up (b: I→(V d)→fps)(k:listens (l:=l) (D:=D) b): Tendsto (fun i=> Stg (posture D (b i)) 0) l (𝓝 (1:Λ d)):= by
 let R:= Λ d; let g i:= (E).branch (raw F d) (probe D (b i));
 have he:= ((E).tends (raw F d) (h.fresh d)).comp k |>.snd_nhds
 have hu : (fun i=> Stg (posture D (b i)) 0) = fun i=> (1:Λ d)+ Matrix.of (g i).val := by simp only [posture,Stg, coeff_zero_eq_constantCoeff_apply,Matrix.of_apply, TestSystem.position_zero]; unfold crib TestSystem.leadingAdjust; rw [h.normal]; rw [diag_one]; rfl
 rw [hu];
 apply Tendsto.mono_right (tendsto_const_nhds (x:=(1:R)) |>.add (show Tendsto (fun i=> Matrix.of (g i).val) l (𝓝 (0:R)) from ?_)) (le_of_eq ?_)
 · exact (E).Z.subtypeL.continuous.continuousAt.tendsto.comp he
 simp
end YM.FormalOPE.RG10.Carryon

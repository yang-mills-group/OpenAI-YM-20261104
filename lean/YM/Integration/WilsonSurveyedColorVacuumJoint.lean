import YM.Integration.WilsonSurveyedColorSubtraction

/-! A map of the actual regulated equation, including its pure-pole and
normalization clauses. Both a change of color and a fixed open-rank
component act on these equations before any limit is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumJoint
open Function Set Filter MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path Oceans
open Landau Alps Garment Shine Hem Mell Pearl Train Dock
open WilsonSurveyedColorQuotient WilsonSurveyedColorPilot WilsonSurveyedColorSubtraction
open scoped Classical BigOperators Topology
variable {G : Gauge}

structure Action (G : Gauge) where
  read : Signal.MH (Mob G)
  scale (a : ℂ) (s : ℝ) (F : Mob G) : read (plow a s F) = plow a s (read F)
  hol {D : Set ℂ} {F : ℂ → Mob G} : Hol D F → Hol D (fun z => read (F z))
  tends {F : ℝ → Mob G} {H : Mob G} :
    Wind F atBot H → Wind (fun s => read (F s)) atBot (read H)
  diff {F : ℝ → Mob G} {H : Mob G} {s : ℝ} :
    speed F H s → speed (fun t => read (F t)) (read H) s

namespace Action
variable (A : Action G)
abbrev tape := tapeL (fun _ : ℂ => A.read)
abbrev film := blast 0 A.tape
theorem atSlot (F : Flats G) (k : ℕ) : A.film F k = A.tape (F k) :=
  by simpa only [Nat.add_zero] using blade 0 F A.tape k

theorem readPage (h : ℕ) (F : Flats G) (y t : ℝ) :
    A.tape (Parade F h y t) = Parade (A.film F) h y t := by
  induction F using Finsupp.induction_linear with
  | zero => rw [map_zero,pageZ,map_zero]
  | add x y hx hy => rw [map_add,page_add,page_add,map_add,hx,hy]
  | single i f =>
    rw [film,blast_sl,Nat.add_zero]
    ext1 z
    change A.read _ = _
    rw [page_sl,page_sl,hikeP,hikeP,map_smul,A.scale]
    rfl

theorem live {f : Coat G} (hf : Live f) : Live (A.tape f) := by
  obtain ⟨F,g,R,hR,hg,he,rfl⟩ := hf
  exact ⟨A.read (g 0),_,R,hR,A.hol hg,he.mono (fun z hz => congrArg A.read hz),rfl⟩

theorem meromorphic {f : Coat G} (hf : mer f) : mer (A.tape f) := by
  obtain ⟨k,hk⟩ := hf
  refine ⟨k,?_⟩
  have h := A.live hk
  apply Live.congr h
  exact Eventually.of_forall (fun z => map_smul A.read _ _)

theorem cool {f : Coat G} (hf : Cool f) : Cool (A.tape f) := by
  refine Submodule.span_induction (p:=fun f _ => Cool (A.tape f)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n,hn,F,rfl⟩
    have h : A.tape (Ice n F) = Ice n (A.read F) := funext fun z => map_smul A.read _ _
    rw [h]
    exact iceC _ _ hn
  · rw [map_zero]; exact (cone G).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]; exact (cone G).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]; exact (cone G).smul_mem c hx

theorem send {h : ℕ} {J X : Flats G} {f p : Coat G} (H : Joint h J X f p) :
    Joint h (A.film J) (A.film X) (A.tape f) (A.tape p) := by
  constructor
  · filter_upwards [H.advance] with z hz
    intro i
    rw [atSlot,atSlot]
    refine ⟨fun s => ?_⟩
    change speed (fun t => plow _ t (A.read (X i z))) (plow _ s (A.read (J i z))) s
    simpa only [A.scale] using A.diff ((hz i).derive s)
  · intro y t
    rw [←A.readPage]; exact A.live (H.toll y t)
  · intro i; rw [atSlot]; exact A.meromorphic (H.wet i)
  · exact A.cool H.ice
  · exact A.meromorphic H.worth
  · intro z t
    exact (A.scale _ _ _).symm.trans (congrArg A.read (H.back z t))
  · filter_upwards [H.sip] with z hz
    rw [atSlot]
    change Wind (fun t => plow _ t (A.read (X 0 z))) atBot (A.read (f z) + A.read (p z))
    simpa only [A.scale,Pi.add_apply,map_add] using A.tends hz

end Action
end YM.Integration.WilsonSurveyedColorVacuumJoint
end

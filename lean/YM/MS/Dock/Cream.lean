import YM.MS.Dock.Earn
/-!
# Uniqueness of Joint responses, up to mer symbol ambiguity away from germ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z J L:Flats G}{K U:Mob G}{f g p q:Coat G}{b c:Bool}{t r:ℤ}{n h ℓ:ℕ}{i:ℂ}
lemma pact_sub_zero (h:Pact (X-F) 0): Pact X F := by intro i; exact ((h i).mono fun j hp=> sub_eq_zero.mp hp) -- Pointwise shape
lemma robe (ht:Joint h 0 F 0 p) : Pact F 0 ∧ p=0 := by
    let H:= ht.ice; have he : Pact F (Finsupp.single 0 p):= by
        intro n; rcases n with _|n
        · rw [Finsupp.single_eq_same]; filter_upwards [ht.advance,ht.sip] with i hi hx; simp only [zero_add] at hx; apply tbase (R:=0) (x:= -(h:ℂ)) _ hx ((ht.back i).stalled) ((ht.back i).view); simpa only [vampV,Finsupp.zero_apply,Pi.zero_apply] using hi 0 -- h shadow
        rw [Finsupp.single_eq_of_ne (show n+1≠0 by omega)]; filter_upwards [ht.advance,(ht.wet (n+1)).price,vamp_up h (n+1),vamp_room h (n+1) ( show n+1>0 by omega )] with i hi hx hw hW; exact found (hi (n+1)) Mell.Trail.zero hx (Form0.zero (b:=false)).price hW hw
    have hv : Spotty (Parade F h 0 0) p:= by obtain hu:= Train.prom he h 0 0; rwa [pureP _ ht.back] at hu; -- $ζ fixed$
    have hu := Live.congr (ht.toll 0 0) hv; obtain ⟨P,hP⟩:= Live.tends hu; obtain rfl|ht':= eq_or_ne p 0; · simpa using he -- orientation pair
    exact (ht' (deep_zero H hP)).elim
lemma uniqueK (hx: Joint h J X f p)(hv: Joint h L Y g q)(he:Pact L J)(hp: Spotty g f): Pact X Y∧p=q:= by
   obtain hz:= Joint.sub hx ((hv.via he).VU hp); rw [sub_self,sub_self] at hz; obtain ⟨H,Hf⟩:= robe hz; exact ⟨pact_sub_zero H,sub_eq_zero.mp Hf⟩
end YM.MS.Dock

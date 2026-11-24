import YM.RG05Readout.Shadows.Stair
/-!
# Turbulence at the newly aggregated multitrace

From authenticated log/gas donor: manufacture whole-germ state one lower
scale, including parent's orientations transmitted on levelling operations.
Part constraints on authentic product values in base orientation, not made true
by reinterpreting reps. Works even reading products not around distinguished
center 0 of any single test geometry. All-center generation expected outside.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N n b p d j:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ} {x e E a:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op n p
local notation "L"=> C.S.block n
local notation "F₀" => Palette C d
local notation "κ₁"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels n
local notation "ν"=> C.path.levels.clock.J
local notation "O"=> Address.Bud C p n
local notation "χ"=> ((C.path.S.block n).val:ℂ)^d
local notation "X'"=> R₀ (n+1)
local notation "X"=> R₀ n
local notation "Ch"=> Address.child C p n
local notation "Z₀"=> C.path.levels.budget
local notation "δ0"=> renal C.path.levels
local notation "TR"=> (fun i:O=> Many.headFee C p n i)
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S)
section
variable (o:Site (C.side n p))(t:Motion) {F:Goods G (C.side (n+1) p)}
local notation "y!"=> fun i:O => affine t.1 ((Ω).ratio.embed o) (Ch i)
local notation "R'"=> (Ω).ratio.embed o
structure Eden (P: Address.Bud C p n→ Three G (C.side (n+1) p))(a:ℝ)(F:Goods G (C.side (n+1) p)) : Prop where
   good i : Useful (X') (P i)
   borne i : (P i).1=stepUp t (y! i) F
   sold i : MergeProof.Float.Blade (X') (y! i) (P i).snd.1 (profile (X'|>.activities) ((P i).snd.2)) 0 a
lemma returns_stairs {n:Side} (t:Motion) (o:Site n){f g:Goods G n} (hp: stepUp t o f=stepUp t o g): f=g:=by
    have he : MergeProof.twist (Motion.backward t) t=(1,false):=by cases t; rename_i a b; cases b<;> simp [Motion.backward,MergeProof.twist]
    let a:= eject t o; have ht:= congr_arg (stepUp (Motion.backward t) a) hp
    rw [step_cycle,step_cycle,he] at ht
    have hy : affine (Motion.backward t).1 a o = 0:=by rw [show o= affine t.1 o 0 from by simp [affine]]; exact Address.unplace _
    rw [hy,MergeProof.Ribbons.stepid,MergeProof.Ribbons.stepid] at ht; exact ht
local notation "pA"=> debit C n d a
local notation "p!"=> Palette C d
abbrev amplitude (C:Family G)(n N p d:ℕ)(w:PulseC)(F:Goods G (C.side (n+1) p)):=journey C p n N d (fun φ=> w φ • F)
variable (w:PulseC){P:Address.Bud C p n→Three G (C.side (n+1) p)} (H:Eden (N:=N) o t P a F) (ht: Cater C D)
include ht hw H h
lemma morning (hm:b ≤ n)(hN:n<N)(hp:d+3 ≤ C.path.levels.clock.J n)(ha:0 ≤ a)(hW:Priced d w 1) : ∃ (Q:O→Tape G (C.side n p))(f g: O→ Palette C d),
    pulseOut (Address.average Q)= amplitude C n N p d w F ∧ (∀ i,Printed C d (X) 0 (κ₁ n) (Q i) (f i) (g i) pA)∧ (∀ i,size (f i) ≤ pA) ∧ ∀ i:O,∀ (φ:Body) (π:(C.path.rep N p n).activities.Moves t.1 o), Cap (d+2) φ 1 → Ride Ω (y! i) o (D N p n hN) χ (scalar t (w (TR i φ)) • P i) (View.spin t π ((Q i) φ)) pA:=by
    have h:=h
    have hX(i:O):∃ (Q:Tape G (C.side n p))(f g:Palette C d), ∃ E, Signpost (X') t R' E (P i) ∧ Course (D:=D N p n hN) (d:=d) (Ch i) ((glyph w E).comp (TR i)) Q f g pA pA ∧ size f ≤ pA ∧ ∀ (φ:Body)(π:(C.path.rep N p n).activities.Moves t.1 o), Cap (d+2) φ 1 → Ride Ω (y! i) o (D N p n hN) χ (scalar t (w (TR i φ)) • P i) (View.spin t π (Q φ)) pA:=by
       obtain ⟨P',h,Q,y,g,hq,he,H⟩:=upright h ht hN w (hw.toll p n N hm hN) hp hW (H.good i) (H.sold i) ha
       refine ⟨Q,y,g,P',h,hq,he,fun φ π hP=>by simpa only [mul_one] using H φ 1 π hP⟩
    choose Q f g A hF hQ hP hR using hX
    refine ⟨Q,f,g,?_,fun i=>(hQ i).paid,hP,hR⟩
    funext φ; obtain ⟨b,hb,Hφ⟩:= Native.Cap.cost φ (d+2); rw [topCell_average]; unfold amplitude journey Address.average; rw [Pi.smul_apply,Finset.sum_apply]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_; let p:=TR i
    have he:= ((hQ i).ready φ b Hφ).exactStep
    have hg:(A i).fst= F ∘ (Lattice.pull 1 (Ch i)):=by
        have ht : MergeProof.twist t (1,false)=t:= by cases t; rename_i a b; cases b<;> simp [MergeProof.twist]
        apply returns_stairs t R'; change stepUp t _ _=stepUp t _ (stepUp (1,false) (Ch i) F); rw [step_cycle,ht, ← (hF i).trade]; exact H.borne _
    rw [show pulseOut (Q i) φ=_ from he]; change _ • ((Ω).push _ ((w (p φ)) • (A i).fst))= _; rw [hg]; rfl
include hv
lemma bornSig (hm:b ≤ n)(hN:n<N)(hp:d+3 ≤ C.path.levels.clock.J n)(ha:0 ≤ a)(hW:Priced d w 1) :
    ∃ Y H,Signature C p b n N d h D V (amplitude C n N p d w F) pA Y H :=by -- Signature types syntax
    obtain ⟨Q,f,g,hF,hT,hY,hP⟩:= morning h hw o t w H ht hm hN hp ha hW
    obtain ⟨s,K,c,β,T,Q',hS,-⟩:= (hw.toll p n N hm hN).author; let t:=hS.cursor.sense d le_rfl
    rw [← hF]; exact Shadow.chamber h hw hv (Address.average Q) (Address.average f) hm hN (snapshotAve (Real.sqrt_pos.mpr (forcedPos C.path.levels n)) (h.wilson.represents N p n hN.le).good t.order t.power hT) (ave_size f hY)
end
end YM.RG05Readout.Shadow

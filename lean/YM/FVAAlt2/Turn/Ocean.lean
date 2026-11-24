import YM.FVAAlt2.Turn.Budget
/-! Apply rotation action already in native D-dimensional laws. Ocean
 transport via compact regulator interpolation. Use `step0` with leading
 clock.Sturdy true U only, commuting with four-axis Spin action. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Motions
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum Outlook
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{i:ℂ}{m n k:ℕ}
variable (s:Spin (L 0))
local notation "B"=> motion G s
variable {U: Rip G} {F:Mob G}{b:Bool}
-- Charge motion doesn't assert preserving unrelated μ-rules (same-spin propagator required).
lemma motion_arbor (V X: Mob G)(hx:Ruddy true U)(hc:closedF U b) : B (arbor U V X)=arbor U ( B V ) ( B X ):= funext fun m=>(hx.turn m _ (fun e=>Bool.noConfusion e)).gatherR (V m) (X m) (hc m) (hc m) -- inference
lemma motion_trueS (h:Sturdy true F) : B F= F:= funext fun m=> h.turn m _ (fun hi=>Bool.noConfusion hi) -- fix binder
lemma motion_scout {f:ℂ→Mob G}(h:Scout f): Scout ((B) ∘ f):= ⟨h.price.elim (fun _ h=>⟨ _,h.1,motion_fell s h.2 ⟩),motion_hol s h.sky⟩
lemma motion_sync {f:ℂ→Mob G}(h:Sync false f): Sync false ((B) ∘ f):=⟨motion_scout s h.eye,fun i hi=> motion_sturdy s ( h.vote i hi )⟩
lemma motion_compact (h:Form0 false F)(hu: RockB U true)(hi:i∈Town): B (ocean i U F) = ocean i U ( B F ):= by
 have hh: RockB U false:= ⟨hu.toKnot.clearer,hu.gear ⟩; refine Sync.drape (motion_sync s (hh.volume0 h.sync)) (hh.volume0 (Form0.sync ( motion_form s h ))) ?_ hi
 intro n; let T:= s.arch (Nat.zero_le n); let K:=flagS T G; have he:= K.leadC (μ:=Px n) T.volume T.turn.toHomeomorph.measurableEmbedding (hu.token.turn n _ (fun e=>Bool.noConfusion e)) (F n) (theory h.price hu.price n) -- hx args
 change B (ocean n U F) n= _; rw [burn,show ocean (↑n:ℂ) U F n =_ from lamp hh (h.sync) n, show ocean (n:ℂ) U ( B F ) n=_ from lamp hh (Form0.sync ( motion_form s h )) n, LinearMapRealm, he]; rfl -- unwrap
lemma motion_drive {X:ℕ→ Mob G}(h:Drift false X F): Drift false (( B ) ∘ X) (( B ) F):= by refine ⟨motion_form s h.real,fun i=> motion_form s (h.ticket i),?_⟩; unfold Function.comp; simp_rw [← map_sub]; exact motion_fell s h.grey
lemma motion_ocean (hx:i∈Town)(hf:Form0 false F)(h:Knot true U): B (ocean i U F)=ocean i U (( B ) F):=by
 apply rockGone (motion_drive s ( oceansLine (steak hf) (newer h.clearer) hx )); unfold Function.comp; simp_rw [motion_compact s hf (tried h _ (being _) (sold _)) hx]; exact oceansLine (steak (motion_form s hf)) (newer h.clearer) hx

abbrev mcoat (G:Gauge)(s:Spin (L 0)) : MH (Coat G):= tapeL fun _ :ℂ=> motion G s
abbrev mswing (G:Gauge)(s:Spin (L 0)): MH (Flats G):= blast 0 (mcoat G s)
local notation "C"=> mcoat G s
local notation "X"=> mswing G s
-- C formal ζ power series *function*, ambiguity from charge contact in port Δ. Therefore retain Pact through end. 
lemma mco(f:Coat G): (C) f i=(B) ( f i ):=rfl
lemma mzero (F: Flats G)(i:ℕ): mswing G s F i=mcoat G s (F i):= blade 0 F _ i -- check
lemma basis_tree (F H:Flats G)(ht: Ruddy true U)(h:closedF U b): X (TreeN U F H)= TreeN U (X F) (X H):= by
    induction F using Finsupp.induction with
    | zero=> simp
    | single_add k a F he hx ih=>
       rw [map_add,map_add,map_add,LinearMap.add_apply,LinearMap.add_apply,map_add] -- investigate
       rw [ih]; refine congr_arg₂ (· + · ) ?_ rfl
       rw [show (X (Finsupp.single k a)) = Finsupp.single k (C a) from blast_sl 0 k C a, TreeN,explode, Finsupp.lsum_single,Finsupp.lsum_single]; simp only [LinearMap.coe_mk,AddHom.coe_mk]; -- use commute Mblast
       ext1 i; by_cases hj:k ≤ i
       · obtain ⟨r,rfl⟩:= Nat.exists_eq_add_of_le' hj
         simp only [mzero, Train.blade]; exact funext fun q=> motion_arbor s _ _ ht h
       rw [mzero,bland (Nat.lt_of_not_le hj), bland (Nat.lt_of_not_le hj), map_zero]
lemma pact_M {V : Coat G}(p:Sun false V)(q:Knot true U): Spotty ( C (swamp U V) ) (swamp U ( C V )):= by
   filter_upwards [high0,sunny p] with i hi he; have H:= motion_form s he; rw [mco,swamp_spec q.clearer he hi, swamp_spec (f:= C V) q.clearer (show Form0 false _ from H) hi,map_smul,motion_ocean s hi he q]; rfl
lemma pact_X {F:Flats G}(H:Moony false F) (q:Knot true U): Pact (X (CycleN U F)) (CycleN U (X F)):= by
   intro i; rw [mzero]; obtain i|i:= i; · rw [CycleN, bland zero_lt_one,bland zero_lt_one, map_zero ]
   rw [CycleN,Train.blade,Train.blade,mzero]; exact pact_M s ( H i ) q
end YM.MS.FVA.Motions

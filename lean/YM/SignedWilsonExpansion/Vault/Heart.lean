import YM.SignedWilsonExpansion.Chron.Impulse
import YM.SignedWilsonExpansion.Stage.Hearty
/-! # Make public the ORIGINAL finite observable (caps/form pipeline), supports,
and extend by linearity only as paid. Shared stochastic history and original turn;
patch the *full actual K letter*, no reconditioning of proper masks. We use F9
rather than require a small-field expansion for the measured word.
-/
set_option autoImplicit false
set_option maxHeartbeats 590000
noncomputable section
namespace YM.Integration.HeartT
open Function Filter Finset MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open OPE.Therm Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries Asymptotics Gauge Source Labels
open SignedWilsonExpansion Homes Dancer Fort Stitch Purchases Purchases.PurchVoice UVClock Schedules HalfRoof StageG
open XSpace Commission WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa
open XSpace.Normalize (leaf)
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{d t i f K v N p q j n:ℕ}
variable (C:Family G){D:Fin n→ ℕ} (Y:C.Makes)
open Logwood Cells
lemma world (N p:ℕ) (Y:C.Makes): scene C.path N p N = law G (C.side N p) (C.beta N p):=by unfold scene law OPE.Therm.dose Wilson.weight; rw [(Y.wilson.starts N p).2]
-- Letters.UNITS. horizon relative prefactors, no renorm difference
include Y
lemma microphone_unit {b:BeamT C}{F:Extraction.Order}{H:(Bel C.book).Hierarchy}{ρ:ℝ} (h:b.Given F H ρ)(p:d≤b.k)(u:b.V.k<N)(s:ℕ) : streak b (leaf G d) N s = C.refUnit d:=by
    apply Eq.trans  (?_: _ = Stitch.worn b (leaf G d) N s 1 ) (pulse_unit b h p u Y); unfold streak Stitch.worn; rw [leafLogo,Pert.Scale.gear_unit]
lemma unitsK (A':C.label d≃ₗ[ℂ] C.label d) (g:ReadyReturn C d N p j n A') (V:PurchVoice C d N p j n) : states C d j N p (j+n) (C.refUnit d) A'=(C.labels.level d).e0:=by
    rw [states,savePage_unit Y g.late.post (( Nat.le_add_right .. ).trans g.age), ← V.unit_touch Y g,LinearEquiv.symm_apply_apply,unitVec,smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ( Complex.ofReal_ne_zero.mpr ( C.S.a_pos _ ).ne' )),one_smul ]
omit Y
section
variable (d A:ℕ)
def feetK (K p:ℕ)(o:Site (C.side K p)) : Finset (Site (C.side K p)) := (C.localSection d).footprint o
abbrev wreath (o:Fin n→Site (C.side K p))(s: Finset (Fin n)) : Finset (Site (C.side K p)) := s.biUnion fun i=> feetK C ( D i ) K p (o i)
/-- family symbols actual uncut product letter.
   `scaled` on core with *rep* threshold, book compatibility in Birth.
-/
def letterK (N p K:ℕ)(y:C.label d)(o:Site (C.side K p)) (U:Config G (C.side K p)):ℂ:= y 0+(C.localSection d).places ((C.labels.level d).scaled (C.path.rep N p K).p.threshold⁻¹ ((C.labels.level d).core y)) o U
lemma leafK (o:Site (C.side K p))(U:Config G (C.side K p)): letterK C d N p K (C.labels.level d).e0 o U = 1 := by
    unfold letterK; rw [ Extra.Histories.Size.unit_core,map_zero ]; simp only [SectionData.places]; simp [ Frame.e0, (C.localSection d).eval_linear.map_zero ] -- QName verify
lemma home_fee (y:C.label d)(o:Site (C.side K p)): LocalOn (feetK C d K p o) (letterK C d N p K y o):= fun U V hi=> congr_arg (y 0 + · ) ((C.localSection d).placed_local o _ U V hi)
lemma letterK_lin (o:Site (C.side K p))(U:Config G (C.side K p)): IsLinearMap ℂ fun y=>letterK C d N p K y o U:=by
    constructor
    · intro i j; unfold letterK; simp only [map_add,SectionData.places,(C.localSection d).eval_linear.map_add,Pi.add_apply]; abel
    intro a x; unfold letterK; simp only [map_smul, SectionData.places,(C.localSection d).eval_linear.map_smul,Pi.smul_apply,smul_add]
end
lemma portion_fee (A: Schedule)(p:ℕ)(h:f≤ K) : parcel A f K=( A.toDepth h p ).count.val:=by
    apply Nat.cast_injective (R:=ℝ); apply mul_left_injective₀ (A.a_pos K).ne'; dsimp only; rw [parcel_size _ h, mul_comm ]; exact (A.embeds_scale (p:=p) _).symm -- Q check
lemma harbor (x: Fin n→ Cover)(p:ℕ)(h:f≤K): location C.S f K p ∘x= wrap (C.side K p)∘ ( pine C.S f K x ):=by
    funext i; unfold Function.comp location; rw [dif_pos h, Ratio.embed_wrap]; unfold pine; rw [portion_fee _ p h]; rfl
section frame
variable (D:Fin n→ℕ) (U:Fin n→ Cover)
-- compiler canonical cost/fits program declarations
abbrev micT (N p f:ℕ)(v:(i:Fin n)→ C.label (D i)) := fun i=> C.O N p (v i) ( location C.S f N p (U i) )
abbrev fieldT (x:(i:Fin n)→ C.label ( D i )) (N p f K:ℕ)(v:Fin n) := letterK C ( D v ) N p K (x v) (location C.S f K p ( U v ))
variable (v':(i:Fin n)→ C.label (D i))
-- Letter funding.Phases.M.Omega law.Gens captures even empty uses actual all support.
def stroke (N p k:ℕ)(f:Fin n→ Config G (C.side k p)→ℂ) (s:Finset (Fin n)) (u:Config G (C.side k p)):ℂ := ∏ i∈s,f i u
abbrev stemN (f N p:ℕ)(s:Finset (Fin n)):= stroke C N p N (micT C D U N p f v') s
abbrev stemK (f N p K:ℕ)(s:Finset (Fin n)):= stroke C N p K (fieldT C D U v' N p f K) s
abbrev natureL (f N p:ℕ)(s:Finset (Fin n)) := Slate (scene C.path N p N) (stemN C D U v' f N p s)
abbrev shelterK (f N p K:ℕ)(s:Finset (Fin n)) := Slate (scene C.path N p K) (stemK C D U v' f N p K s)
-- care about order.If h
abbrev born₀ (f N p v K:ℕ)(s:Finset (Fin n)):= if h:v≤K then actualTransport C (N:=N) ( stemK C D U v' f N p K s ) h 1 else 0
lemma fullT (Y:C.Makes): macroT C D U f N p v'= natureL C D U v' f N p univ:=by
    rw [natureL, world C _ _ Y]; rfl
lemma lodgeTop (C:Family G)(F:Config G (C.side N p)→ℂ) (Y:C.Makes) : C.omega N p F=Slate ( scene C.path N p N) F := by rw [world C _ _ Y]; rfl
-- Actual inherited. Use allTower Mood.States (not exposing yv)
private lemma keeps (F:Config G (C.side K p)→ℂ) (Y:C.Makes)(hK: K≤N)(w:v≤K)(he:Envelope F): Envelope (actualTransport C (N:=N) F w):=by
    induction w using Nat.decreasingInduction with
    | self=> rw [actualTransport_base C Y hK]; exact he
    | of_succ k hk hg=> rw [actualTransport_step C Y hK _ hk]; exact vote_lodge _ Y (hk.trans_le hK) hg
lemma flow_salary (Y:C.Makes)(hK:K≤N)(w:v≤K): Mood (scene C.path N p K) (scene C.path N p v) (fun F=> actualTransport C (N:=N) (p:=p) F w ) :=by
    refine ⟨fun x p=> keeps C x Y hK w p,fun x p=> ?_,fun z=>funext (fun V=>actualTransport_const C Y hK z w V)⟩; induction w using Nat.decreasingInduction with
    | self=> rw [actualTransport_base C Y hK]
    | of_succ k hk hg=> rw [actualTransport_step C Y hK _ hk]; exact ((older Y ( hk.trans_le hK )).salary _ ( keeps C x Y hK hk p )).trans hg
variable (S: Finset (Fin n))
lemma stroke_env (K N p:ℕ)(f:Fin n→ Config G (C.side K p)→ℂ)(he:∀ i,Envelope (f i)): Envelope (stroke C N p K f S):=by
    have u (s:Finset (Fin n)): Envelope ( stroke C N p K f s ):=by
       induction s using Finset.induction_on with
       | empty=>
           have x: stroke C N p K f ∅=fun _=>1:=by funext y; rw [stroke,Finset.prod_empty]
           rw [x]; exact (⟨measurable_const,1,fun _=>norm_one.le⟩: Envelope fun _:Config G (C.side K p)=> (1:ℂ))
       | @insert i s h hi=> exact ( show stroke C N p K f (insert i s)= f i*stroke C N p K f s from funext (fun y=> Finset.prod_insert h) ).symm ▸ envP (he i) hi
    exact u S
lemma plantN (i:Fin n): Envelope (micT C D U N p f v' i):=by exact Envelope.compactC ( C.continuousO .. ) -- find
lemma plantK (i:Fin n): Envelope (fieldT C D U v' N p f K i):=by
    unfold fieldT letterK; apply Envelope.compactC; exact continuous_const.add ((C.localSection _).continuous_places .. )
-- cumu package.Apply.Ear.Cost
variable {U Q:ℕ}
structure Sheet (G:Gauge) (C:Family G) (F:Fin 3→ Config G (C.side K p)→ ℂ) (w:v≤K) (N:ℕ):Prop where
    story (M:(Config G (C.side K p)→ℂ)→ Config G (C.side v p)→ℂ)(h:M=(fun T=> actualTransport C (N:=N) T w)) : Mood (scene C.path N p K) (scene C.path N p v) M ∧
      let μ:=scene C.path N p v
      let Q':=fun i j=> M (F i* F j)-M (F i)* M (F j)
      Cumu (Slate (scene C.path N p K)) (F 0) (F 1) (F 2)= Slate μ (fun U=> Cumu (fun f=> M f U) (F 0) (F 1) (F 2))+Cov μ (Q' 0 1) (M (F 2))+Cov μ (Q' 0 2) (M (F 1))+Cov μ (Q' 1 2) (M (F 0))+Cumu (Slate μ) (M (F 0)) (M (F 1)) (M (F 2))
lemma firstSheet (F: Fin 3→ Config G (C.side K p)→ ℂ)(w:v≤K)(Y:C.Makes)(he:K≤N)(pH:∀ i, Envelope (F i)) : Sheet G C F w N :=by
   refine ⟨fun x y=>y.symm ▸ (?_) ⟩; let Y₀:= flow_salary (p:=p) C Y he w; let _:=probability (p:=p) Y.wilson he; let _:=probability (p:=p) Y.wilson ( w.trans he ); exact ⟨Y₀, conditional _ Y₀ ( F 0 ) ( F 1 ) ( F 2 ) (pH _) (pH _) (pH _)⟩ -- infer?
end frame
end YM.Integration.HeartT

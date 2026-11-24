import YM.Contacts.Milling.Masque
/-! Canonical rank-two functional for EVERY positive grade. Doesn't subtract just a bare quadratic rank;
     determines coupling reset. Rank 3 and 4 via same Ward. No curvature lift needed in update. -/
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {α β X Y :Type}{n m:Side}{t k j:ℕ}{b c:ℝ}{G:Gauge}{F:bore G}{P:bore G}
variable {s η:ℝ≥0}{e i:ℕ} {B H: TableFee}
structure Light (P:bore G) : Prop where
   my : Cradle _ P
   protects (k:ℕ)(m:Side): sealed (hair P m) (k+3)
lemma should {H:Bed}(h:Blazing F H): Light F:= ⟨h.frame,fun k m=> h.beams m k⟩
def moon (X:bore G)(m:Side)(k e:ℕ) := Kale.mirror (fire (wind (hair X m) k e)) ∘ input G m
lemma glowstar (h:Light F)(m:Side)(k e:ℕ)(hk:e < k+3) : Pointwise (moon F m (k+3) e):= evidence _ (planted (h.protects k m e hk))
lemma certifiedStar (h:Light F)(m:Side)(k e:ℕ)(hk:i+e<k+3)(u:Link G m): jet (moon F m (k+3) e) i u=if 2 ≤ i + e then design (hair F m (i+e-2) i) u else 0:= by
   rw [nightwalk (glowstar h m k e (by omega)).analytic (wind_ana ..) (survives (h.protects k m e (by omega))) i (by omega) u, wind_jet,if_pos hk,Nat.add_comm i,grate]
-- Use moons at convenient common k (lives all at compile-time). high though no arithmetic cost from caps.
private abbrev empire (i:ℕ):Side:= ⟨i+1,by omega⟩
private lemma pace : Tendsto (fun j=>(empire j).val) atTop atTop:= tendsto_atTop_mono (f:=id) (show ∀ i,id i≤ (empire i).val from Nat.le_succ) tendsto_id
lemma inkstars (h:Light F)(hs:Roof s F B) (m:Side)(k e:ℕ)(hk:t+1+e<k+3)(ht:2≤ t+1+e) : Recorded (mask (G:=G) (F (t+1+e-2) (t+1))) (moon F m (k+3) e) 0:= masked _ (hs.shelter ..) (h.my.poem _ _) (fun x=> h.my.here x _ _) (glowstar h _ _ _ (by omega)).analytic (fun x=> (certifiedStar h _ _ _ hk x).trans (if_pos ht))
lemma ink_two (h:Light F)(hs:Roof s F B)(m:Side)(e:ℕ) : Recorded (mask (G:=G) (F e 2)) (moon F m (e+5+3) e) 0:= by
   let he := inkstars (t:=1) h hs m (e+5) e (by omega) (by omega); convert he using 2; congr 2; omega
lemma tollWitness (hG:G.Simple)(h: Light F)(ht: Roof s F B)(hs:0<s)(e:ℕ) : TributeColor (mask (G:=G) (F e 2)) ((s:ℝ)/((1:ℕ)+1)) (B e 2) Universal:= point_receipt hG (F:=fun i=> moon F (empire i) (e+5+3) e) (ε:=fun _=>0) pace (shadow_face _ _ (ht.shelter e 2) hs) tendsto_const_nhds (fun i=> by simpa using ink_two h ht (empire i) e) (fun i=> glowstar h _ _ _ (by omega))
lemma strokeAgreed (hG:G.Simple)(h: Light F) (m:Side) (e:ℕ): fderiv ℝ (moon F m (e+5+3) e) 0=0:= by
  have he:=point_quiet hG (glowstar h m (e+5) e (by omega)) 1 one_lt_two zero_lt_one; refine ContinuousLinearMap.ext fun v=>?_ ; simpa using DFunLike.congr_fun he (fun _=>v)
-- canonical cost & tilt σ independent
-- Real test from the momentum coefficient of the complete log-functional Hessian (factorial normalized).
def salvia (G:Gauge)(i:G.ColorIndex)(P: Field (Fin 2) (Node (Dye G))):= alphaPay i (mask P)
def senior (G:Gauge)(i:G.ColorIndex)(P:bore G):Prop := ∀ e,0< e→ salvia G i (P e 2)=0
def salve (i:G.ColorIndex)(P:bore G):Prop:=∀ e,salvia G i (P e 2)=0 -- rest only
lemma salute (hG:G.Simple)(x:G.ColorIndex)(h:Light F)(ht:Roof s F B)(hs:0<s)(e:ℕ)(hv:salvia G x (F e 2)=0): softRank 3 (F e 2):= by
    have he:= tollWitness hG h ht hs e; let P:= mask (G:=G) (F e 2); have hz:leapTip P (step (0:Axis)) 1 ![x,x]=0:= by
       rw [← he.true_tip (he.crop_edict (fun _ _=>trivial))]; norm_cast; linarith only [(show 2*(leapTip P (step (0:Axis)) 1 ![x,x]).re=0 from hv)]
    intro b; let j:= Prod.snd ∘ b; let k:= Prod.fst ∘ b; exact (he.vanish hG 1 0 (by decide) x hz j k).weaker (by norm_num)
lemma soften (hG:G.Simple)(x:G.ColorIndex)(h:Light F)(ht:Roof s F B)(hs:0<s)(e:ℕ)(hv:salvia G x (F e 2)=0) : softRank 2 (F (e+1) 3) ∧ softRank 1 (F (e+2) 4):= by
    let V i:= moon F (empire i) (e+5+3) e; have he i : Pointwise (V i):= glowstar h _ _ _ (by omega); have H : LawfulSum 3 empire V 1 := ⟨mask (G:=G) (F e 2),⟨_,_,shadow_face _ _ (ht.shelter e 2) hs⟩,fun i=> ink_two h ht _ e,fun i j=> salute hG x h ht hs e hv (fun a=>(j a,i a))⟩
    let U:=mask (G:=G) (F (2+1+e-2) (2+1)); let W:=mask (G:=G) (F (3+1+e-2) (3+1)); obtain ⟨hU,hW⟩:= pure_grey pace he (fun i=>strokeAgreed hG h _ _) H U W (shadow_face _ _ (ht.shelter _ _) hs) (fun i=> inkstars h ht _ _ _ (by omega) (by omega)) (shadow_face _ _ (ht.shelter _ _) hs) (fun i=> inkstars h ht _ _ _ (by omega) (by omega))
    rw [show e+1=2+1+e-2 from by omega,show e+2=3+1+e-2 from by omega]; exact ⟨fun b=>hU (Prod.snd∘b) (Prod.fst∘b),fun b=>hW (Prod.snd∘b) (Prod.fst∘b)⟩
lemma rank_one (hG:G.Simple)(h:Light F)(hp: Roof s F B)(i:ℕ): F i 1=0:= by
   have he (m:Side) : printShadow (F i 1) m=0:= by
      let e:=i+1; let V:=moon F m (e+5+3) e; let P:= printShadow (F i 1) m; have hv (x:Link G m): design P x=0:= by
         have he:= certifiedStar (i:=1) h m (e+5) e (by omega) x; rw [if_pos (show 2 ≤ 1+e from by omega),show 1+e-2=i from by omega,jet, iteratedFDeriv_one_apply,strokeAgreed hG h m e] at he; rw [ContinuousLinearMap.zero_apply,mul_zero] at he; exact he.symm
      funext p; let b:=p 0; let u:Link G m:= Pi.single b 1; change P p=0; have ha:=hv u; rw [design_spec,sum_eq_single p] at ha; · simpa [u,Fin.prod_univ_one,b] using ha
      · intro q _ h; have he:q 0≠b:=fun he=>h (funext fun i=> by rw [Subsingleton.elim i 0]; exact he); simp [u,Fin.prod_univ_one,he]
      simp
   let P (j:ℕ):= printShadow (F i 1) (empire j); refine shadow_compare (k:=P) pace (hp.shelter _ _) (Pulse.Rooted.tranquility (terrain s _)) (fun j=> ⟨printFeeds (heritage (fun p=>h.my.here p i 1) _),?_⟩); unfold P; rw [he]; exact Shadow.empty _
-- units via leading momentum price. h from Awake attaches H m floor.Suffices.
lemma altocumulus {b:Bed} (h:Blazing F b)(hs:Roof s F B)(hw:Whole b.metric)(hu:(b.metric.acts m)ᵀ=b.metric.acts m): Recorded (slots b.metric G) (moon F m (0+5+3) 0) 0:= by
  let V:= moon F m (0+5+3) 0; let T:= Link G m; let M:= spindle G m b.metric; let Q x y:= x ⬝ᵥ (M*ᵥ y)
  have hx x y : Q x y=Q y x:= by unfold Q; rw (occs:=.pos [1]) [← show Mᵀ=M from (tensor_transpose G _).trans (congr_arg (FreeResolvent.tensor G) (pem m hu)), dotProduct_transpose_mulVec]
  have he : ∀ x y:T, iteratedFDeriv ℝ 2 V 0 ![x,y]= Q x y := Work.F03.hessian_polar (glowstar (k:=5) (should h) m 0 (by norm_num)|>.analytic.contDiffAt) (Q:=Q) (fun i j k=> add_dotProduct i j _) hx fun x=> by
     have hh : jet V 2 x= design (hair F m 0 2) x:= (certifiedStar (i:=2) (should h) m (0+5) 0 (by norm_num) x).trans (if_pos (by decide)); unfold jet at hh; rw [(h.pri m).glow,show (fun _:Fin 2=> x)=![x,x] from funext fun i=>by fin_cases i <;> rfl] at hh; unfold Q M; norm_num [Nat.factorial] at hh; linarith only [hh]
  apply according hw.safe; intro x y; rw [show iteratedFDeriv _ _ _ _ _=Q x y from he x y]; unfold Q M spindle; erw [component_dot]; simp_rw [component_mul]; rfl
lemma stark_cash (he:0<s) {b:Bed} (h0:b.metric.read 0=1)(h:Blazing F b)(hs:Roof s F B) (hw:Whole b.metric) (hu:∀ m,(b.metric.acts m)ᵀ=b.metric.acts m)(x:G.ColorIndex) : salvia G x (F 0 2)=1:= by
   obtain ⟨d,D,hd,H⟩:= hw; let H':= slots b.metric G; let V:= mask (G:=G) (F 0 2)
   have hV (i j) : V i j ∘ axes= H' i j ∘ axes:= by
      let W k:= moon F (empire k) (0+5+3) 0; ext1 p; obtain ⟨y,u,hU,hP⟩:= fleet empire pace (axes p) (axes_real p)
      exact tendsto_nhds_unique (Stationary.harvest (F:=W) (ε:=fun _=>0) (shadow_face _ _ (hs.shelter 0 2) he) (fun i=> by simpa using ink_two (should h) hs (empire i) 0) tendsto_const_nhds p y u hU hP i j) (Stationary.harvest (F:=W) (ε:=fun _=>0) (slots_cost (G:=G) hd H) (fun i=>by simpa using altocumulus (F:=F) h hs ⟨_,_,hd,H⟩ (hu (empire i))) tendsto_const_nhds p y u hU hP i j)
   have hz: leapTip V (step (0:Axis)) 1 ![x,x]=_:= (show leapTip V (step (0:Axis)) 1 ![x,x]= leapTip H' _ 1 ![x,x] from congr_arg (fun W: Stationary.Track→ℂ=> speedy W 2 (step (0:Axis))) (funext (fun i=>congr_fun (hV ![x,x] ![coord 1, coord 1]) (roads i))))
   change 2* (leapTip V _ _ _).re=1; rw [hz,show leapTip H' _ _ _=_ from tip_fuel x H hd h0]; norm_num
end
end YM.Contacts.Milling.Lumen

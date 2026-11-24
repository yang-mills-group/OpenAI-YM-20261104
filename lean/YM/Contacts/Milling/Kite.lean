import YM.Contacts.Milling.Steam
/-! Keep towers' deterministic basis in a fixed vertical release independent of period & horizon.
     Row accounting ∥·∥ at planted supports; cover winding & large period passage. -/
noncomputable section
namespace YM.Contacts.Milling.Steam
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open scoped Topology BigOperators Classical Matrix NNReal
variable {α β X Y Z :Type}{b d e:ℝ}{s η:ℝ≥0}{r k:ℕ}
variable {G:Gauge}{S:Patch}{K:KernelChoices}{c f n m: Side}{W: Stairs G S.L}
def adopt (X:Type)(ψ:Type)[DecidableEq X]: Row X (ψ ⊕ X) := fun x q=> q.elim (fun _=>0) (unitRow X x)
lemma adopt_cost (X ψ : Type) [DecidableEq X] (s:ℝ≥0): Row.strip (adopt X ψ) s 1 := by
    rintro x (u|v); · simp [adopt,Width]; change SumBudget _ 1; exact budget_loosen (budget_zero) zero_le_one
    exact Work.F08.strip_unit x v
lemma offspring_paid (t:StepData c f): installed t.ratio (adopt (Cellar G t.patch.L) (Dye G))= shave t G:= by
   ext i ⟨x,v|v⟩
   · simp [installed,adopt,shave,offspring,Row.acts,FreeResolvent.insertion]
   let u:= splitCo t.ratio (Dye G); let p:= Cellar G t.patch.L; change Row.acts (adopt (Cellar G t.patch.L) (Dye G)) c (u i) (x,Sum.inr v)= _
   have hu : Row.acts (adopt p (Dye G)) c (u i) (x,.inr v)=(unitRow p).acts c (u i) (x,v):= rfl
   let r (p:Co c (Cellar G t.patch.L)) : Yard G t:= (p.1,.inr p.2); have h : Injective r:= by rintro ⟨i,u⟩ ⟨j,w⟩ h; simpa [r] using h
   have ht : u i=(x,v) ↔ offspring t (G:=G) i=(x,Sum.inr v) := (h.eq_iff (a:=u i) (b:=(x,v))).symm; erw [hu,acts_unit,Matrix.one_apply]; simp only [shave,FreeResolvent.insertion,Matrix.transpose_apply,Matrix.of_apply]; split_ifs <;> first | rfl | contradiction| grind

def axisSky (G:Gauge)(S: Patch)(U:Row (Cellar G S.L) (Dye G)) : Row (Mixed G S) (Dye G):= fun a=> a.elim (unitRow (Dye G)) U
def axisLine (G:Gauge)(S:Patch)(U:Row (Cellar G S.L) (Cellar G S.L)): Row (Mixed G S) (Mixed G S) := fun a b=> a.elim (fun _=>0) fun a=> b.elim (fun _=>0) fun b=>U a b
def ax (G:Gauge)(H:FreeResolvent.FaceRow): Row (Dye G) (Dye G):= fun a b=> if a.2=b.2 then krow H a.1 b.1 else 0
variable {t:StepData c f}
lemma skytop (S:StepData c f)(U:Row (Cellar G S.patch.L) (Dye G)):
    (axisSky G S.patch U).acts c= Forge.sky S G (installed S.ratio U) := by
   ext ⟨i,q|q⟩ j; · apply congr_fun (congr_fun (acts_unit (α:=Dye G) c) (i,q)) j -- mism unit
   let h:=splitCo S.ratio (Dye G); change U.acts c (i,q) j= U.acts c (h (h.symm (i,q))) j; erw [Equiv.apply_symm_apply]; rfl
lemma skims (B:Bed)(W:Stairs G t.patch.L)(h:Whole B.metric) (hv:Cabinet (brick G t.patch t.kernel.penalty B) W): (axisLine G t.patch (prom W)).acts c=Matrix.of (veer t G B.metric):= by
   ext ⟨i,a|a⟩ ⟨z,b|b⟩ <;> first | (simp [axisLine,Row.acts,veer,issue h hv]<;> rfl)| skip
lemma axo (n:Side)(H:FreeResolvent.FaceRow)(h:Whole H): Row.acts (ax G H) n=spindle G n H:= by
   unfold spindle; rw [← Krow_acts _ h]; ext ⟨x,a,b⟩ ⟨u,i,d⟩; by_cases he:b=d<;> simp [ax,krow,he,Row.acts,FreeResolvent.tensor]
lemma ax_shape (G:Gauge)(H:FreeResolvent.FaceRow)(h:(krow H).strip s b)(he:0≤b): (ax G H).strip s b := by rintro ⟨a,b⟩ ⟨x,d⟩; unfold ax; split; apply h; exact budget_loosen (by simpa [Width] using (show SumBudget (fun z:Cover=>Real.exp ((s:ℝ)*size z)*‖(0:ℝ)‖) 0 from by simpa using budget_zero)) he
lemma sky_shape {U:Row (Cellar G S.L) (Dye G)} (h:U.strip s b)(he:0≤b): Row.strip (axisSky G S U) s (1+b) := by rintro (a|a) j; apply budget_loosen (Work.F08.strip_unit (α:= Dye G) (η:=s) a j) (by linarith); exact budget_loosen (h a j) (by linarith)
lemma line_shape {U:Row (Cellar G S.L) (Cellar G S.L)} (h:U.strip s b)(he:0≤b): Row.strip (axisLine G S U) s b:= by
   have hz : Width (α:=Axis) (s:ℝ) b (fun _=> (0:ℝ)):= budget_loosen (by simpa [Width] using (show SumBudget (fun z:Cover=>Real.exp ((s:ℝ)*size z)*‖(0:ℝ)‖) 0 from by simpa using budget_zero)) he -- Width implicit
   rintro (a|a) (v|v)<;> first | apply h | apply hz
-- period-independent templates. scalars emptied (shadow estimates never touch r=0).
abbrev bore (G: Gauge) := House (Node (Dye G))
abbrev basinP (G: Gauge)(P:Patch) := House (Node (Mixed G P))
def clan (Q:ChartRatio G)(P:Patch) (U:KernelChoices)(F:bore G) : basinP G P := fun e r=> compote (hoist (install (L:=P.L) (α:=Dye G) (adopt (Cellar G P.L) (Dye G))) (F e r)) (sparkles P Q r) (fireworks P U G r) e
lemma clan_shape (G:Gauge)(Q:ChartRatio G)(F:bore G)(h:Shaped F) : Snug (clan Q S K F):= by
   refine ⟨fun i j=> compote_seed hoist_shape (print_even _) (print_even _),fun i j hi=> compote_zero hi ?_⟩; intro hh; rw [h.thin i j (.inr hh),hoist_empty]
-- operate covers (normalization/reset released after read). require beyond-strip budget for Hess only in passage of §lighting.
structure Cradle (α:Type)(A:House (Node α)) : Prop extends Shaped A where
    here (x:Cover): Dorm (backpack x) A
    scalar (i:ℕ): A i 0=0
variable {F:bore G}{V:bore G}{Q: ChartRatio G}{Fee:TableFee}{B H:Bed}{A:Cross t.patch.L (TypeFace 1) (TypeFace 1)}{W: Stairs G t.patch.L} -- rename duplicate
lemma cradle_shape {P:House (Node α)}(h: Cradle α P): Shaped (hair P n):= ⟨fun i j=> shadowEven (heritage (fun a=> h.here a i j) _) (h.poem i j), fun i j hi=> by rw [hair,h.thin i j hi,printLull]⟩
lemma compote_adapt {V:Equiv.Perm X}{F G H:Field (Fin k) X}(h:Mirrored V F)(hg: Mirrored V G)(hp:Mirrored V H): Mirrored V (compote F G H r):= by intro x; unfold compote; split_ifs<;> simp [*,h _,hg _,hp _]
lemma clan_pure (Q:ChartRatio G)(h:Cradle (Dye G) F) : ∀ x:Cover, Dorm (backpack x) (clan Q S K F):= fun x i j=> compote_adapt (dent (h.here (S.L.val • x) i j) (fun _ _=> plot_inertia ..)) (aboard_hold _ _ _) (aboard_hold _ _ _)
section cost
variable (σ:ℝ≥0)
def loaded (Q:ChartRatio G) (P:Patch)(K:KernelChoices) (j r:ℕ) (A:ℝ) : ℝ := let t:= station P K; let U:=Mixed G P;
    cargo (templates G P) σ (words (luck G P Q) r)+ (cargo (crafts t (G:=G)) σ (words (piloted (G:=G) t 0) r)+(Fintype.card (Cellar G P.L)*beamPrice σ 1*A*(Fintype.card U*beamPrice σ 1)^(r-1)))
-- cargo arg order
lemma compote_cost {l:Range X}{F G H:Field (Fin k) X}(h:Rooted l F b)(hg: Rooted l G d)(hp:Rooted l H e): Rooted l (compote F G H r) (d+(e+b)):= by
    let z (a:ℝ)(hp:0≤a) : Rooted l (0: Field (Fin k) X) a:= (Rooted.tranquility l).weaken (fun _=>le_rfl) hp
    unfold compote; split
    next p=> exact z _ (add_nonneg hg.cash (add_nonneg hp.cash h.cash))
    apply Rooted.add _ <| Rooted.neg (.add ?_ h); · split; exact hg; exact z _ hg.cash
    split; exact hp; exact z _ hp.cash
lemma compote_desc {l:Range X}{F G H:Field (Fin k) X}(h:Rooted l F b)(hg: Rooted l G d)(hp:Rooted l H e){p : X→Y}{P Q R:Field (Fin k) Y}(hF:Shadow p F P)(hG:Shadow p G Q)(hH:Shadow p H R): Shadow p (compote F G H r) (compote P Q R r):= by
    have hx (A B:Field (Fin k) X)(U Z:Field (Fin k) Y){d e}(hA:Rooted l A d)(hB:Rooted l B e)(hY:Shadow p A U)(hZ:Shadow p B Z): Shadow p (A+ -(B+F)) (U+ -(Z+P)):= hY.add (by simpa only [neg_one_smul] using (hZ.add hF hB h).scale (-1)) hA (hB.add h).neg
    unfold compote; split_ifs <;> first| apply Shadow.empty| exact hx _ _ _ _ hg hp hG hH| exact hx _ _ _ _ hg (Rooted.tranquility ..) hG (Shadow.empty p)| exact hx _ _ _ _ (Rooted.tranquility ..) hp (Shadow.empty p) hH| exact hx _ _ _ _ (Rooted.tranquility ..) (Rooted.tranquility ..) (Shadow.empty p) (Shadow.empty p)
lemma clan_closes {e r: ℕ} (V:House (Co f (Dye G))) (h:(σ:ℝ)/t.patch.L.val≤ (η:ℝ))(hv:Cradle (Dye G) F)(he:Rooted (terrain η _) (F e r) b)(hl:Shadow (lower f) (F e r) (V e r)) : Two (voyageW c σ _) (clan Q t.patch t.kernel F e r) (banners G t Q V e r) (loaded σ Q t.patch t.kernel e r b) 0 := by
   let P:= t.patch; let A:= adopt (Cellar G P.L) (Dye G); have hp:= ledgers (adopt_cost (Cellar G P.L) (Dye G) σ) zero_le_one; have hr : Pulse.Ripple (terrain η _) (terrain σ _) (access P.L σ (α:=Dye G) (β:=Mixed G t.patch)) := influx h; have hx:= hoist_pay (t:=access P.L σ) hr hp he;
   apply together_due (heritage (fun a=> clan_pure Q hv a e r) c) (compote_cost hx (aboard_summed ..) (aboard_summed ..))
   unfold clan banners; erw [← offspring_paid t]; exact compote_desc hx (aboard_summed ..) (aboard_summed ..) (hoist_period hr hp he hl (st_new t.ratio _)) (aboard_desc _ _ _) (aboard_desc _ _ _)
end cost
-- Curtain normalization actual comes later
variable (G)
def kin (H: FreeResolvent.FaceRow) (r:ℕ): Pulse.Field (Fin r) (Node (Dye G)) := if h:r=2 then takeRank h.symm ((2:ℝ)⁻¹ • printRun (both (plane (ax G H)))) else 0
variable {G}
def kiss (A:House X) : House X:= fun i r=> if r=0 then 0 else A i r
def caravan (Q:ChartRatio G) (P:Patch)(K:KernelChoices)(Y: bore G)(W:Stairs G P.L)(H: FreeResolvent.FaceRow): bore G:= kiss (mintage (kin G H) (plane (axisSky G P (Origin.stretch P K G W))) (plane (axisLine G P (prom W))) (clan Q P K Y))
lemma kin_shape (G:Gauge)(H:FreeResolvent.FaceRow) (r:ℕ): Poem (kin G H r) ∧ ∀ x, Mirrored (backpack x) (kin G H r):= by
  unfold kin; split
  next ht=> subst r; refine ⟨Poem.scale (print_even _) _,fun x=> bend (print_mirror _ (fun u=> by simp [Spine.both, plane, backpack])) _⟩
  exact ⟨Poem.empty,fun _ _=>rfl⟩
lemma caravan_flow (Q:ChartRatio G)(P:Patch)(K:KernelChoices)(h: Cradle (Dye G) F)(W:Stairs G P.L)(H:FreeResolvent.FaceRow): Cradle (Dye G) (caravan Q P K F W H):= by
   let X := mintage (kin G H) (plane (axisSky G P (Origin.stretch P K G W))) (plane (axisLine G P (prom W))) (clan Q P K F); have ha:= clan_shape G (K:=K) (S:=P) Q F h.toShaped; refine ⟨⟨?_,?_⟩, ?_, fun i=> by simp [caravan,kiss]⟩
   · intro i j; unfold caravan kiss mintage; split_ifs<;> first| apply Poem.empty| exact (kin_shape ..).1 | exact Poem.minus hoist_shape
   · intro i j hi; unfold caravan kiss mintage; split_ifs with hx hu; · rfl
     · unfold kin; rw [dif_neg (by omega)]
     rw [(massaged_shape ha).thin i j (.inr (by omega)), hoist_empty,neg_zero]
   intro x i r; unfold caravan kiss mintage; split_ifs; · exact fun x=>rfl
   · exact (kin_shape ..).2 x
   intro y; apply congr_arg Neg.neg ((dent (R:=plane (axisSky G P (Origin.stretch P K G W))) (w:=x) (v:=x) (levitate (G:=plane (axisLine G P (prom W))) (fun i j => by simp [plane,backpack] ) (clan_pure (S:=P) (K:=K) Q h x) i r) (fun i j=> by simp [plane,backpack])) y) -- wrong
lemma kin_desc (n:Side) (H: FreeResolvent.FaceRow)(h:Whole H)(hp:(krow H).strip s b)(hb:0≤b)(hη:(2*η:ℝ)≤s)(r:ℕ): Two (voyageW n η (Dye G)) (kin G H r) (circ G n H r) ( (2:ℝ)⁻¹ * ((Fintype.card (Breed 1 (Dye G)):ℝ)*b)) 0:= by
   have hv:= ax_shape G H hp hb; apply together_due (heritage ((kin_shape ..).2) n); unfold kin; split
   next ht=> subst r; convert (Rooted.smul (Rooted.even (arrive_both hv hb hη)) ((2:ℝ)⁻¹)) using 1 <;> first| rfl| simp
   exact (Rooted.tranquility (terrain η (Dye G))).weaken (fun _=>le_rfl) (by positivity)
   unfold kin circ; split_ifs; next ht=> subst r; have hl:= title (row_ship (ax G H) n); rw [axo n H h] at hl; exact (hl.even (arrive_both hv hb hη)).scale _
   apply Shadow.empty
lemma carav_roll (P: Patch)(K:KernelChoices)(W:Stairs G P.L)(n: Side)(h:Cradle (Dye G) F)(H:FreeResolvent.FaceRow)(hH:Whole H): Chest (hair (caravan Q P K F W H) n) H:= by
   obtain ⟨s,C,hs,hp⟩:= k_capacity hH; lift s to ℝ≥0 using hs.le
   have hB:0≤ C:= Extra.Iteration.Cost.nonneg (hp (coord 0) (coord 0))
   refine ⟨cradle_shape (caravan_flow Q P K h W H),?_⟩; intro x; rw [← circ_read G n H x]; congr 1
   let Y:= caravan Q P K F W H; change hair Y n 0 2=circ G n H 2; have he: Y 0 2=kin G H 2:= by simp [Y,caravan,kiss,mintage]
   have hv:= (kin_desc (G:=G) n H hH hp hB (η:=0) (by simp) 2); unfold hair; rw [he]; -- owes shadow Z'
   obtain ⟨Z,hZ,hp⟩:=hv.owes; suffices h: Z=circ G n H 2 by exact h ▸ focused (printFeeds hv.risen) (lower_onto n) hZ
   funext t; symm; apply sub_eq_zero.mp; exact norm_le_zero_iff.mp (hp.bound t 0)

namespace Fare
def star (Q:ChartRatio G) (P:Patch)(K:KernelChoices)(s:ℝ≥0)(F:TableFee) : TableFee:= fun i j=> loaded s Q P K i j (F i j)
def stamp (P:Patch)(G:Gauge)(b:ℝ)(r:ℕ)(a:ℝ):= (Fintype.card (Mixed G P)*b)*a*(Fintype.card (Dye G)*b)^(r-1)
variable (Q:ChartRatio G)(P:Patch)(K:KernelChoices)(s:ℝ≥0)(B:TableFee) (d b u:ℝ)(e r:ℕ)
def single : TableFee:= Pulse.sky (levity ((Fintype.card (Mixed G P):ℝ)*b) (star Q P K s B))
-- h width H quoted separately.
def boot := if e=0 then (2:ℝ)⁻¹ * ((Fintype.card (Breed 1 (Dye G)):ℝ)*u) else stamp P G d r (single Q P K s B b e r)
def turns := if e=0 then 0 else stamp P G d r (Pulse.sky (lowland ((Fintype.card (Mixed G P):ℝ)*b) ((Fintype.card (Mixed G P):ℝ)*b) 0 (star Q P K s B) 0) e r)
end Fare
structure Roof (s:ℝ≥0)(Q:House (Node α))(B:TableFee):Prop where
    shelter i j: Rooted (terrain s _) (Q i j) (B i j)
section
variable (σ:ℝ≥0)(A: Spine.voyage t.patch.L)(W:Stairs G t.patch.L)(Q:ChartRatio G) (P:House (Lines G f 1)) (hF: Cradle (Dye G) F) (hB:Whole B.metric)(hH:Whole H.metric)(hw:Cabinet (brick G t.patch t.kernel.penalty B) W)(hq: Inputs t (installed t.ratio A) (B.metric.acts f) (H.metric.acts c))
variable {u a v x:ℝ} (hi:(σ:ℝ)/t.patch.L.val≤ (η:ℝ))(hp: Roof η F Fee)(hz:∀ i r,Shadow (lower f) (F i r) (P i r))(hW: W.strip σ b)(he:0≤ b)(hx:Row.strip (axisSky G t.patch (Origin.stretch t.patch t.kernel G W)) σ d)(hd:0≤d) (hv:(krow H.metric).strip ((2:ℝ)*σ) u)(hu:0≤u)
include hF hB hH hw hq hi hp hz hW he hx hd hv hu
lemma tell (i r:ℕ) (hr:r≠0): Two (voyageW c σ _) (caravan Q t.patch t.kernel F W H.metric i r) (Forge.vault t Q P (installed t.ratio A) B.metric H.metric i r) (Fare.boot Q t.patch t.kernel σ Fee d b u i r) (hush σ c* Fare.turns Q t.patch t.kernel σ Fee d b i r):= by
   unfold Fare.boot Fare.turns caravan kiss Forge.vault mintage; rw [if_neg hr]; by_cases hz0:i=0; · simp only [hz0,↓reduceIte,mul_zero]; apply kin_desc c H.metric hH (s:=2*σ) ?_ hu _ _ <;> first| exact (by simpa using hv)| simp
   simp only [if_neg hz0]; let X:= Mixed G t.patch; let Y:= clan Q t.patch t.kernel F; let K:= axisLine G t.patch (prom W); let L:= axisSky G t.patch (Origin.stretch t.patch t.kernel G W); have hl : K.strip σ b:= line_shape (brace W hW he) he
   have hz1:= flight_stem hl he; let z:ℝ:=Fintype.card X*b; have HH: Track (terrain σ X) (plane K) z := ⟨hz1.left,hz1.rows,hz1.columns⟩; have hs:= torch (n:=c) HH (row_ship K c) (fun x y z=>by simp [plane,backpack]); have hX (i j :ℕ): Two (voyageW c σ _) (Y i j) (banners G t Q P i j) (Fare.star Q t.patch t.kernel σ Fee i j) ((0:TableFee) i j) := clan_closes σ _ hi hF (hp.shelter i j) (hz i j)
   let c':= hush σ c; have hh := hoist_comp L c hx hd (completed hs hX i r)
   have hy : K.acts c=Matrix.of (veer t G B.metric):= skims B W hB hw
   have hh': L.acts c= Forge.sky t G (atr G t (installed t.ratio A)):= by unfold L; rw [skytop,rise_roll W hB hw hW he hq]; rfl
   erw [hh',hy] at hh; have hl : ∀ (k i j:ℕ), lowland z (c'*z) 0 (Fare.star Q t.patch t.kernel σ Fee) 0 k i j= c'*lowland z z 0 (Fare.star Q t.patch t.kernel σ Fee) 0 k i j:= fun k i j=>by simpa only [mul_zero,smul_zero] using wakeup_fees z z 0 c' 0 (Fare.star Q t.patch t.kernel σ Fee) 0 k i j
   let he:=hh.scale (-1); rw [neg_one_smul ℝ,neg_one_smul ℝ,norm_neg,norm_one,one_mul,one_mul] at he; convert he using 1 <;> try rfl
   unfold Fare.stamp Pulse.sky; unfold c' at hl; simp_rw [hl,←mul_sum]; unfold z X; ring
end
end YM.Contacts.Milling.Steam

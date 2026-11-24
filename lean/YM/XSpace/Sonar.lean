import YM.XSpace.Reverb

/-!
# Exact unconditioned mark readings as tariffed lines

Forward-difference line of the right order. Useful at two-variable endpoint expansion,
singular near-zone bounds (ordOne) and contact normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Trace
open Scale Lattice Sail Litter Further.FreeCovariance.KP Function Filter Set Finsupp MvPolynomial Outline Next.Rank.Normal
open scoped Topology BigOperators ContDiff
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F] {G:Gauge}
-- successive diffs: cost lattice magnitude and Taylor mode. charge-space real.
def riff (k:Axis) : Module.End ℝ (Line G):= displace (step k)- LinearMap.id
def gate : List Axis → Module.End ℝ (Line G)
| []=> LinearMap.id
| k::l=>riff k ∘ₗ gate l
lemma pit_riff (k:Axis)(L:Line G)(p:Contact G):probe (riff k L) p=probe L (zone (step k) p-p):=by rw [riff,LinearMap.sub_apply,map_sub,map_sub,LinearMap.sub_apply,born];rfl
lemma opus (x:Cover)(k:Axis)(L:Line G): displace x (riff k L)=riff k (displace x L):=by unfold riff; rw [LinearMap.sub_apply,LinearMap.sub_apply,map_sub,displacement x, displacement,add_comm x];rfl
lemma toll (x:Cover)(l:List Axis)(L:Line G):displace x (gate l L)=gate l (displace x L):=by induction l with | nil=>rfl | cons i l ih=> change displace x (riff i (gate l L))=_; rw [opus,ih];rfl
lemma in_gate (x:UnitIndex G)(l:List Axis)(p:Contact G) : probe (gate l (needle x)) p= crack l (twig x.1.2 p) x.1.1 x.2 := by
  induction l generalizing p with
  | nil=> rw [gate,LinearMap.id_coe,id_eq,probes];rfl
  | cons i l ih=> change probe (riff i _ ) p=_; rw [pit_riff,ih,map_sub,twig_zone,snack]; rw [show ∀ A:Cover→G.Color,sweep (step i) A-A=Δf i A from fun A=> funext fun x=> by change A (step i+x)-A x=_; rw [add_comm (step i)];rfl]

structure Rudder (G:Gauge) (k:ℕ) where
  head : UnitIndex G
  layout : Fin k → Axis
namespace Rudder
variable {k:ℕ}
def worth (b:Rudder G k):=gate (List.ofFn b.layout) (needle b.head)
end Rudder
variable {k d:ℕ}
def cane (k:ℕ)(G:Gauge):=Submodule.span ℝ (Set.range (Rudder.worth (k:=k) (G:=G)))
lemma gated (x:UnitIndex G)(l:List Axis):gate l (needle x) ∈ cane l.length G:= Submodule.subset_span ⟨⟨x,l.get⟩,by unfold Rudder.worth; simp⟩
lemma tariff (L:Line G): L∈ cane 0 G:=by
  induction L using Finsupp.induction_linear with
  | zero=> exact (cane 0 G).zero_mem
  | add _ _ h h' => exact (cane 0 G).add_mem h h'
  | single i a=> rw [show single i a=a • needle i by simp [needle]]; exact (cane 0 G).smul_mem a (show needle i∈cane 0 G from gated i [])

-- explicit curl readouts, Ward identity inherited. first native edge diff + address

def touch (x:Cover)(i j: Axis)(l:List Axis)(c:G.ColorIndex): Line G:= gate (l++[i]) (needle ((x,j),c)) - gate (l++[j]) (needle ((x,i),c))
lemma append_single (l:List Axis)(d:Axis)(p:Cover→F): crack (l++[d]) p=crack l (teeth d p):=by induction l with | nil=> rfl | cons i l ih=> exact congr_arg (Δf i) ih
lemma paid (x:Cover)(i j:Axis)(l:List Axis)(c:G.ColorIndex)(A: Contact G): probe (touch x i j l c) A = crack l (crackle i j A) x c:=by rw [touch,map_sub,LinearMap.sub_apply,in_gate,in_gate,append_single, append_single]; unfold crackle; simp_rw [LinearMap.sub_apply, ← peaked]; rw [map_sub,Pi.sub_apply,PiLp.sub_apply];rfl
lemma touch_cane (x:Cover)(i j:Axis)(l:List Axis)(c:G.ColorIndex): touch x i j l c ∈ cane (l.length+1) G:=by
  apply (cane (l.length+1) G).sub_mem; exacts [by simpa using gated (G:=G) ((x,j),c) (l++[i]),by simpa using gated (G:=G) ((x,i),c) (l++[j])]

open RG Wilson Labels Source Source.Drops
open Next.Rank CellsInt Beamer
variable {H:Hol G} (S:Survey G H d)
def input (p : Contact G): Horizon G:= fun i=> crackle i.2.1.val.1 i.2.1.val.2 p i.1 i.2.2
lemma survey_hits (u:Labels.Key G)(p:Contact G): Survey.component u (Chart2.primary S (0:Cover) p)=Cross.readKey S u (input p):=by
  rw [Cross.readKey,Cross.uses]; unfold Chart2.primary; congr 1; apply congr_arg S.extract; funext i; ext1 j; let t:= S.looks i; change Chart2.linearFace (G:=G) (t.offset,t.plaq) p j= crackle (F:=G.Color) t.plaq.val.1 t.plaq.val.2 p t.offset j; rw [plot _ _ t.plaq.property]

def ping (v:Labels.Key G): Line G:=∑ i: Top.Bean S, Top.bills S (Survey.component v) i • touch (S.looks i.1).offset (S.looks i.1).plaq.val.1 (S.looks i.1).plaq.val.2 [] i.2
lemma ping_at (v: Labels.Key G)(A:Contact G): probe (ping S v) A=Cross.readKey S v (input A):= by unfold ping; rw [map_sum, LinearMap.sum_apply,Cross.price_print]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,LinearMap.smul_apply, paid];rfl
lemma pulses (v:Labels.Key G)(x:Cover): Chart2.leftKey S x v=harp (displace x (ping S v)):=by
  have he : Chart2.leftKey S x v=volume x (Chart2.leftKey S (0:Cover) v):=by
    have he (x:Cover): Chart2.leftKey S x v=Chart2.p0 S x (X v):=by simp [Chart2.toy,Chart2.p0]
    rw [he, he 0,stained,Chart.pull0]; simp [Chart.lug]
  rw [← rings,he]; apply congr_arg (volume x); apply Chart2.same; intro A; rw [Chart2.pit_left,leg_test,ping_at,← survey_hits S]; rfl
lemma shuttered (A:Contact G)(i j:Axis):Beamer.polar (input A) i j=crackle i j A:=by
  have he (i j:Axis)(h:i < j):Beamer.polar (input A) i j=crackle i j A:=by ext x l; exact poll_at _ i j x h l
  rcases lt_trichotomy i j with h|h|h; exact he i j h; subst i; ext x l; simp [Beamer.polar,crackle]; rw [Beamer.reverse,he j i h, crackle, crackle, LinearMap.sub_apply, LinearMap.sub_apply, neg_sub]
lemma signal_s (A:Contact G): shutter (input A):=by
  intro i j k; simp_rw [shuttered]; change Δf i _+Δf j _+Δf k _=_
  funext x; simp only [Pi.add_apply,Δf,crackle_ap,add_right_comm x,Pi.zero_apply]; abel
lemma pings (v:Labels.Key G): Stops (ping S v):=by intro A; rw [ping_at,show input (stream A)=0 from funext fun i=>by unfold input; rw [stream_curl];rfl,map_zero]
private lemma germ_hit (A:Contact G)(p:Degree G): Beamer.gesture p (input A)=probe (touch p.point p.a.val.1 p.a.val.2 (List.ofFn p.layout) p.paint) A:=by
  have he (l:ℕ)(t:Fin l→Axis)(P:Cover→G.Color): jumps l t P=crack (List.ofFn t) P:=by induction l generalizing P with | zero=> rw [List.ofFn_zero];rfl | succ l ih=>rw [jumps,List.ofFn_succ,snack]; exact ih (Fin.tail t) (Δf (t 0) P)
  rw [gesture_hits,shuttered,he,paid]
lemma allows (v:Labels.Key G): ping S v∈ cane (v.1+1) G:=by
  by_cases h : generation v≤ d; swap; · rw [show ping S v=0 from inquire (by ext1 A; rw [ping_at,Cross.unused S v (not_le.mp h),map_zero];rfl)]; exact (cane _ G).zero_mem
  obtain ⟨r,K,T⟩ := Cross.removes _ (Cross.blossoms S (Survey.component v)) (Cross.startsKey S v h); let f (i:Cross.Reading G v.1 r):= let p:= Cross.mood i; touch p.point p.a.val.1 p.a.val.2 (List.ofFn p.layout) p.paint
  have he:ping S v=∑ i, K i • f i:=by
    apply inquire; ext1 A; rw [ping_at, show Cross.readKey S v _= _ from T (input A) (signal_s A),map_sum, LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,LinearMap.smul_apply,germ_hit];rfl
  rw [he]; apply (cane _ G).sum_mem; intro i _; apply (cane _ G).smul_mem; let p:= Cross.mood i; simpa [show v.1=p.degree from rfl] using touch_cane p.point p.a.val.1 p.a.val.2 (List.ofFn p.layout) p.paint
lemma caned_early {v:Line G}(ht:v∈cane k G)(h:d<k)(A:Vase d G.Color): probe v (release A)=0:=by
  suffices v∈LinearMap.ker (probe.flip (release A)) from this; apply (Submodule.span_le.mpr _) ht; rintro v ⟨f,rfl⟩; rcases f with ⟨x,t⟩; change probe (gate (List.ofFn t) (needle x)) _= _; rw [in_gate]; change felt (half x.1.2) (A _) _ _ _= _; rw [late _ _ (by simpa using h)]; rfl
lemma toll_due (v:Labels.Key G)(A:Tune (v.1+1) G.Color)(h:generation v≤d): probe (ping S v) (release A.val)= (Labels.axes G v.1).coord v.2 (Maxwell.gaugeJet (ink A)):=by
  rw [ping_at]; let x:= ink A; rw [← Cross.end_cost S v h]; obtain ⟨r,K,T⟩ := Cross.removes _ (Cross.blossoms S (Survey.component v)) (Cross.startsKey S v h); rw [← show Cross.looks S (Survey.component v)=Cross.readKey S v from rfl, T _ (signal_s _),T (Beamer.sweep v.1 (Maxwell.gaugeJet (ink A))) (Beamer.shutters (Maxwell.gaugeJet x))]
  apply Finset.sum_congr rfl; intro i _; let p:=Cross.mood i
  have he: p.degree=v.1:=rfl
  congr 1; rw [germ_hit, paid,sounds]
  change felt _ (_:Stamp p.degree G.Color) _ _ _= Cross.actsOn p.degree (gesture p) x
  rw [sent _ _ _ p.layout,Cross.actual_leg];rfl
end YM.XSpace.Trace

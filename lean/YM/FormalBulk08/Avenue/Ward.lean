import YM.FormalBulk08.Avenue.Tune
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
lemma Extras.shifts {J:Type}(g:J→I)(h:Extras W):Extras (W.wturn g):= Soft.reach h (turnLeaf W.scrolls g)

def horizonB (W:Lab G K I)(x:Leaf W.scrolls)(i j:edgeL G):= aura fun n=> bandP G (location (W.V x.a) n x.b) K.penalty i j
lemma exposures (W:Lab G K I)(x:Leaf W.scrolls)(i j:edgeL G):let A:= fun n=>bandP G (location (W.V x.a) n x.b) K.penalty i j; Ends A (horizonB W x i j) ∧ ‖horizonB W x i j‖ ≤ mediumP G K (W.lower x) ∧ ∀ n,x.b≤n→ ‖A n-horizonB W x i j‖≤ mediumP G K (W.lower x)*fare_n x n:= by
    intro A; let B:= mediumP G K (W.lower x); have hx:=fee_live G K _ ((W.V x.a).clock.adm x.b)
    have he n (hn:x.b≤n) m (hm:n≤ m):‖A n-A m‖≤B*fare_n x n:= hx.fade (W.V x.a) _ _ _ rfl hn hm _ _
    have hp:Ends A (horizonB W x i j):= aura_pays A (fun n=> B*fare_n x n) (fare_fin_lt x B) ((eventually_ge_atTop x.b).mono fun n hn m hm=>he n hn m hm)
    exact ⟨hp,le_of_tendsto' hp.norm (fun n=>hx.cords _ _ _),fun n hn=>le_of_tendsto ((tendsto_const_nhds.sub hp).norm) ((eventually_ge_atTop n).mono fun m hm=> he n hn m hm)⟩
variable {E R:ℕ}{ρ:ChartRatio G}{F:Frame G d}{T:SectionData F}{H:Source.Hol G}
-- limit retaining l/e and test norm at same root. upper book limit Wick operations
variable (W)
def WLimit (a:hue G)(ρ:ChartRatio G)(F:Frame G d)(T:Source.SectionData F)(h:d+1≤D)(i:Leaf W.scrolls): Matrix (Letter F) (Letter F) ℝ:= Matrix.of fun j k=> pearlJ F (pageant (horizonB W i) (Drift.issue W ρ a F T h i.a i.b k (Pose.inside F j D) 0) d (slots F j)) (mint F j)
def WLocal (a:hue G)(ρ:ChartRatio G)(F:Frame G d)(T:Source.SectionData F)(h:d+1≤D)(i:Leaf W.scrolls)(N:ℕ): Matrix (Letter F) (Letter F) ℝ:= Woven F (location (W.V i.a) N i.b) K.penalty (bornY ρ W a F T h i.a N i.b)
variable {W}
variable (h:Use W ρ E)(q:Quota F H W o D E R)(v:LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hR:d≤R)(u: Extras W) (a:hue G)
include h q v hs ht hb hR u
lemma bough (r:ℕ)(i:Letter F):
    let T' N p (x:meshPoint W):= pageant (bandP G (location (W.V x.a) N x.b) K.penalty) (bornY ρ W a F T q.horizon x.a N x.b i p 0)
    Brass (aurum W) o (fun x=>W.width x.a x.b) (purseR targetPower) (fun _=>1) (fun x p=>T' x.top p x d r) (fun x p=>pageant (horizonB W x.toLeaf) (Drift.issue W ρ a F T q.horizon x.a x.b i p 0) d r):= by
    have hx := Soft.reach u (fun x:meshPoint W=>x.toLeaf)
    intro X; refine stature_pay (I:=meshPoint W) (o:=o) hx (fun x=>(fee_live G K _ ((W.V x.a).clock.adm x.b)).active) (fun i=>(h.zero i.toLeaf).le) (fun i=> (ratioR_pos ..).le) (fun x i j=> (fee_live G K _ ((W.V x.a).clock.adm x.b)).cords (location (W.V x.a) x.top x.b) i j) (fun x i j=>(exposures W x.toLeaf i j).2.1) (fun x i j=>(exposures W x.toLeaf i j).2.2 x.top x.wing) (?_) d
    intro r; have he:= (expend q h v hs ht hb a hR (Nat.zero_le E) r i).left
    obtain ⟨C,hC,M,H⟩:= Drift.skiff q h v a hs ht hb hR (Nat.zero_le E) i r; have ht:=hC.reach (fun x:meshPoint W=> x.toLeaf);
    refine ⟨he,⟨_,ht,fun _=>M _,fun x p=>?_⟩,_,ht,fun _=>M _,fun x p=>?_⟩
    · simp only [one_mul];exact (H x.toLeaf p).1
    simp only [one_mul];rw [←mul_assoc]; exact ((H x.toLeaf p).2 x.top x.wing)

lemma patrons (i j:Letter F): Pact (aurum W) (purseR targetPower) (fun x=> WLocal W a ρ F T q.horizon x.toLeaf x.top i j) (fun x=>WLimit W a ρ F T q.horizon x.toLeaf i j):= by
    let X:= meshPoint W; let V(x:X):=W.windowD x.toLeaf; let τ:= aurum W; let n:=slots F i; let Q(x:X):=amounts F H W o D E R x.toLeaf
    obtain ⟨⟨A,k,m,hA⟩,⟨B,e,b,hB⟩,C,hC,c,hx⟩:=bough h q v hs ht hb hR u a n j; have he (x:X):= q.supply h x.toLeaf
    let U(x:X)(p):= winner (location (W.V x.a) x.top x.b) K.penalty d (bornY ρ W a F T q.horizon x.a x.top x.b j) p n
    let Y(x:X)(p):= pageant (horizonB W x.toLeaf) (Drift.issue W ρ a F T q.horizon x.a x.b j p 0) d n
    let f:= Pose.inside F i D; have hp : Soft τ Q:= q.running.reach (fun x:X=>x.toLeaf)
    let M(_p:X)(S:Tile (edgeL G) n):= pearlJ F S (mint F i)
    have hU (x:X)(S:Tile (edgeL G) n)(A)(ht:Knoxville (fame _) (V x) (0,o) S A): |M x S| ≤ Q x*A:= ((he x).pupils _ (by unfold n;have hq:=slotsFits F i; omega)).pays _ A ht i
    have he'(x:X): M x (U x f-Y x f)=M x (U x f)-M x (Y x f):= by
        apply eq_sub_of_add_eq; unfold M;rw [←chalk F (U x f-Y x f) (Y x f) (hx x f) (hB x f) (h.zero x.toLeaf) (h.zero x.toLeaf), sub_add_cancel]
    have ht1:= (hp.times (k.times (soft_coin _ (1*‖f‖)))).below (g:=fun x=>M x (U x f)) fun i=> (hU i _ _ (hA i f)).trans (le_abs_self _); have ht2:= (hp.times (e.times (soft_coin _ (1*‖f‖)))).below (g:=fun x=>M x (Y x f)) fun i=> (hU i _ _ (hB i f)).trans (le_abs_self _); refine ⟨ht1,ht2,_,hp.times (hC.times (soft_coin _ ‖f‖)),fun i=>mul_nonneg (he i).plus (mul_nonneg (c i) (norm_nonneg _)),fun x=>?_⟩
    change |M x (U x f)-M x (Y x f)|≤ _; rw [←he' x]; exact (hU x _ _ (hx x f)).trans_eq (by ring)
end YM.FormalBulk08.Avenue

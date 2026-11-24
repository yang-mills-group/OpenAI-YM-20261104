import YM.X.Site.Maze
/-!
Characteristic graded scalar propagator on the periodic Cover. Explicit formula on row-row.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Print
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric
open Reed Stems Hinge Braid Fielding
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "H"=> Hair G
variable (x y z:Cover)(f g:Fan G)(p:Hair G)(A:Brush G)
abbrev GridF:=Side→Cover→Cover→ℝ
def graphK (D:List Axis)(u:Cover):GridF:= fun n x y=> Interval.grads D green (wrap n (x-y+u))
lemma slopeX (l:List Axis)(i: Axis): graphK l z n (x+step i) y-graphK l z n x y=graphK (i::l) z n x y := by unfold graphK; rw [Interval.grads,differ,show x+step i-y+z= x-y+z+step i by abel,map_add,wrap_step]
lemma slopeY (l:List Axis)(i:Axis): graphK l z n x (y+step i)-graphK l z n x y=-(graphK (i::l) (z-step i) n x y):= by
   unfold graphK; rw [Interval.grads,differ]; rw [show x-(y+step i)+z=x-y+(z-step i) by abel, ← wrap_step n i, ← map_add, show x-y+(z-step i)+step i=x-y+z by abel,neg_sub] -- slope
lemma p₁ (i:Axis)(l:Fin k→Axis): spend n x y (jetRow _ l (pointB (step i) p)) g= spend n (x+step i) y (jetRow _ l p) g:= by rw [← jets_lead, spend_subx]
def ls : (k:ℕ)→(Fin k→Axis)→List Axis | 0,_=> [] | k+1,x=> x 0 :: ls k (Fin.tail x)
def markS : (k:ℕ)→(Fin k→Axis)→Cover | 0,_=>0 | k+1,x=>step (x 0)+markS k (Fin.tail x)
lemma sign_foot (l:Fin k→Axis): (ls k l).length=k:= by induction k with| zero=>rfl| succ k IH=>rw [ls,List.length_cons,IH]
variable (t: Hair G)
def matchK (p t:H):ℝ:= if p.2=t.2∧p.1.2=t.1.2 then 1 else 0
lemma twins (i:Axis):matchK (pointB (step i) p) t=matchK p t:=rfl
lemma dye : spend n x y (Finsupp.single p 1) (Finsupp.single t 1)=matchK p t*graphK [] (p.1.1-t.1.1) n x y:= by
    rw [spend_single]; unfold tau pointB Braid.cane matchK; split_ifs; rw [one_mul,one_mul,one_mul,graphK,← map_sub,show x+p.1.1-(y+t.1.1) = x-y+(p.1.1-t.1.1) by abel];rfl -- mul_one line wrong
    simp
lemma cruise (b:Fin m→Axis): spend n x y (Finsupp.single p 1) (jetRow m b t)= (-1:ℝ)^m *matchK p t *graphK (ls m b) (p.1.1-t.1.1-markS m b) n x y:= by
    induction m generalizing y with
    | zero=> rw [ls,markS,sub_zero,pow_zero,one_mul]; exact dye ..
    | succ m IH=>
        let i:=b 0; let l:=Fin.tail b; have he : jetRow (m+1) b t= jetRow m l (pointB (step i) t)-jetRow m l t:=by rw [jetRow]; unfold pointB;rw [add_comm t.1.1]
        rw [he,map_sub, ← jets_lead, spend_suby, IH,IH, ← mul_sub,slopeY]; rw [pow_succ,markS,ls,show p.1.1-t.1.1-(step (b 0)+markS m l)=p.1.1-t.1.1-markS m l-step (b 0) by abel]; unfold i l;ring
lemma dictate (l:Fin k→Axis)(b:Fin m→Axis): spend n x y (jetRow k l p) (jetRow m b t)=(-1:ℝ)^m*matchK p t * graphK (ls k l++ls m b) (p.1.1 - t.1.1 - markS m b) n x y:= by
    induction k generalizing x with
    | zero=> exact cruise ..
    | succ k IH=>
       let i:=l 0; let A:= Fin.tail l; have he: jetRow (k+1) l p= jetRow k A (pointB (step i) p)-jetRow k A p:=by rw [jetRow]; unfold pointB; rw [add_comm p.1.1]
       rw [he,map_sub,LinearMap.sub_apply,p₁,IH,IH, ← mul_sub,slopeX]; rfl

def bird (k:ℕ) : Submodule ℝ GridF:= Submodule.span ℝ {a|∃ D:List Axis, D.length=k ∧ ∃ u:Cover,a=graphK D u}
lemma graph_bird (l:List Axis)(v:Cover)(he:l.length=k):graphK l v∈bird k:= Submodule.subset_span ⟨l,he,v,rfl⟩
-- doubles as symbolic graphK description for distributions. order exactly k.
lemma enrolled (b:Fin m→Axis)(h:f∈Reed.grads G k): (fun (n:Side)(x y:Cover)=> spend n x y f (jetRow m b p))∈ bird (k+m):= by
    induction h using Submodule.span_induction with
    | mem i h=> obtain ⟨⟨l,p'⟩,rfl⟩:=h; unfold Function.uncurry; simp_rw [dictate]; exact Submodule.smul_mem _ _ (graph_bird (ls k l++ls m b) _ (by simp [sign_foot])) -- cast? explicit
    | zero=> simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add a z h g t u=>simp only [map_add,LinearMap.add_apply];exact Submodule.add_mem _ t u
    | smul a z h t=> simp only [map_smul,LinearMap.smul_apply]; exact Submodule.smul_mem _ a t
lemma enrolled₂ (h:f∈Reed.grads G k)(hp:g∈Reed.grads G m): (fun (n:Side)(x y:Cover)=> spend n x y f g)∈ bird (k+m):= by
    induction hp using Submodule.span_induction with
    | mem i hp=> obtain ⟨⟨l,p'⟩,rfl⟩:=hp; exact enrolled f p' l h
    | zero=> simp only [map_zero];exact Submodule.zero_mem _
    | add a z h g t u=> simp only [map_add]; exact Submodule.add_mem _ t u
    | smul a z h t=> simp only [map_smul];exact Submodule.smul_mem _ a t
end YM.PositionX.Print

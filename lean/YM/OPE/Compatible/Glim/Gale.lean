import YM.OPE.Compatible.Glim.Nup
/-! # family roll and rank, price commitment -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J:Type}{n:Side}
abbrev foliage (G:Gauge):=(n:Side)→Site n→ScriptJ (Bid.Dir G n)
abbrev Shut (q:Z→ℝ)(A: Z→ foliage G)(k m:ℕ):Prop:=∀ i:Phase,Take q (fun t n x y=> (A t n x y).seq i.val) (k+i.val) m
variable {q v:Z→ℝ}{A B:Z→ foliage G}
lemma Shut.add (h:Shut q A k m)(hp:Shut q B k m):Shut q (A+B) k m:=by intro i;fin_cases i<;>first|exact (h 0).add (hp 0)| exact (h 1).add (hp 1)|exact (h 2).add (hp 2)
lemma Shut.taller (h:Shut q A k m)(hz:q≤v)(hp:k≤d): Shut v A d m:=fun i=> Take.raise (h i) hz (Nat.add_le_add_right hp _)
noncomputable abbrev tooth (p:Token):Phase→ℝ:=fun i=>p.seq i.val
lemma Shut.neg (h:Shut q A k m): Shut q (-A) k m:=by
     intro i; apply Take.congr ((h i).scale (-1)) (?_); intro z; filter_upwards with n; funext x v; fin_cases i<;>  change (-1:ℝ)*_= -_<;> ring_nf <;> rfl
lemma Shut.sub (h:Shut q A k m)(hp:Shut q B k m): Shut q (A-B) k m:=by rw[sub_eq_add_neg]; exact Shut.add h hp.neg
lemma Shut.prod (h:Shut q A k m)(hp:Shut v B l m): Shut (q*v) (A*B) (k+l) m:=by
     have ht(p s t:Phase)(he:p.val+s.val=t.val): Take (q*v) (fun i n x y=> tooth (A i n x y) p * tooth (B i n x y) s) (k+l+t.val) m:= Take.raise (Take.product (h p) (hp s)) le_rfl (by omega); intro j; fin_cases j; exact ht 0 0 0 rfl; exact Take.add (ht 0 1 1 rfl) (ht 1 0 1 rfl); exact Take.add (Take.add (ht 0 2 2 rfl) (ht 1 1 2 rfl)) (ht 2 0 2 rfl)
lemma Shut.sum (F:I→Z→ foliage G)(s:Finset I)(h:∀ i∈s,Shut q (F i) k m): Shut q (∑ i∈s,F i) k m :=by induction s using Finset.induction_on with
     | empty=> rw[sum_empty]; intro i; fin_cases i<;> exact Take.zero _
     | insert i s ht ih=> rw[sum_insert ht]; exact Shut.add (h i (mem_insert_self ..)) (ih (fun i hp=>h _ (mem_insert_of_mem hp)))
variable (e:RootEdge)(u:G.ColorIndex)
lemma HeadSet (a:G.Color)(b:Bool) : Shut (Z:=Z) 1 (fun _ n x=> Mount (sett n x e) a b u) 0 m:=by
     intro i; let p(_:Unit):= e; let L:Libra.Keys G Unit→L[ℝ] G.Color:= ContinuousLinearMap.proj (); let f: Libra.Keys G Unit→ℝ:= (Phone G).coord u ∘ Cast b a ∘ L; have h: ContDiffAt ℝ ω f 0:= ((Phone G).coord u).toContinuousLinearMap.contDiff.contDiffAt.comp 0 ((show ContDiffAt ℝ ω (Cast b a) (L 0) from L.map_zero.symm ▸ cast_sm b a).comp _ L.contDiff.contDiffAt)
     rw[Nat.zero_add]; have ht: Take (Z:=Z) 1 (fun _ n x=> jet (f∘ dip p n x) i.val) i.val m:= monaJet f p h i.val m; refine ht.congr (fun j=>?_); filter_upwards with n; funext x y; fin_cases i<;>rfl
variable (b:Bool)
lemma Tow {P:Z→foliage G}(hp:∀ u:G.ColorIndex,Shut q (fun i n x=> Pry (functorE x e u) (P i n x)) k m): Shut q (fun i n x=>Topper (sett n x e) ((Phone G) u) b (P i n x)) k m:=by
     let F(j:G.ColorIndex)(i:Z)(n:Side)(x:Site n):= Mount (sett n x e) ((Phone G) u) b j * Pry (functorE x e j) (P i n x); have he(j): Shut q (F j) k m:= by rw [← one_mul q, ← Nat.zero_add k]; exact Shut.prod (HeadSet e j ((Phone G) u) b) (hp j)
     rw [show (fun i n x=>Topper _ _ _ _)=∑ j,F j from ?_]; exact Shut.sum _ _ (fun i _=> he i); funext i n x; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rfl
end YM.OPE.Variance

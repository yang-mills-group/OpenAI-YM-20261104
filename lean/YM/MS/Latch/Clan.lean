import YM.MS.Latch.Circuit
/-!
# Differences of bilinear operations and size flags.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff
variable {G:Gauge} {b c:Bool} {s t r:ℤ} {I E F':Type}{F H U W:Law G}{K Y:Edge G}{μ:Measure QP}{A:QP}
local notation "Ψ"=> field ( Landau.parity ( A:=Axis ) (C:=G.ColorIndex))
-- lapse contact namespace
variable {w: Legs (Lane4 G)}
def SatC (μ:Measure QP)(K:Edge G)(F:Law G)(b:Bool): Prop:=∀ w,Course b w→ Integrable (fun q=> trc K q F w) μ
def SatP (μ:Measure QP)(K: Edge G)(F H:Law G)(A:QP): Prop:=∀ (i j:BH G)(l r: Legs (Lane4 G)), Integrable (fun p=> Tone.bill A p*meshZ K i j F H l r p) μ
lemma of_cyc (hu:SatC μ K F b)(hv:SatC μ K U b)(hw:Course b w): cycle K μ (F+U) w = cycle K μ F w+cycle K μ U w:= by unfold cycle; simp_rw [map_add, Pi.add_apply]; exact integral_add (hu w hw) (hv w hw)
lemma of_subc (h: SatC μ K F b)(hp:SatC μ K H b)(hw:Course b w): cycle K μ (F-H) w= cycle K μ F w - cycle K μ H w:= by unfold cycle; simp_rw [map_sub,Pi.sub_apply]; exact integral_sub (h w hw) (hp w hw)
lemma other_subc (h:SatC μ K F b)(hp:SatC μ Y F b)(hw:Course b w) : cycle (K-Y) μ F w= cycle K μ F w-cycle Y μ F w:= by
    unfold cycle; have hv(q:QP): trc (K-Y) q F w=trc K q F w-trc Y q F w:= by simp_rw [at_trc,Pi.sub_apply,sub_mul, Finset.sum_sub_distrib]
    simp_rw [hv]; exact integral_sub (h w hw) ( hp w hw)
lemma sift (h:SatP μ K F H A)(hv: SatP μ K U H A) : Cabin A K μ (F-U) H= Cabin A K μ F H-Cabin A K μ U H:= by
    funext w; unfold Cabin; have he (i j:BH G)(l r:Legs (Lane4 G))(q:QP): meshZ K i j ( F-U ) H l r q= meshZ K i j F H l r q - meshZ K i j U H l r q:= by simp [meshZ,mul_sub,sub_mul]; -- semicolon bug
    rw [Pi.sub_apply]; simp_rw [he,mul_sub,integral_sub (h ..) (hv ..), Finset.sum_sub_distrib,mul_sub]; exact map_sub (allocate Ψ w) _ _
lemma sift' (h: SatP μ K F H A)(ht: SatP μ K F W A): Cabin A K μ F ( H-W ) = Cabin A K μ F H-Cabin A K μ F W:= by
    funext w; unfold Cabin; have he (i j: BH G)(l r:Legs (Lane4 G))(q:QP): meshZ K i j F (H-W) l r q= meshZ K i j F H l r q- meshZ K i j F W l r q:= by simp [meshZ,mul_sub];
    rw [Pi.sub_apply]; simp_rw [he,mul_sub,integral_sub (h ..) (ht ..), Finset.sum_sub_distrib,mul_sub]; exact map_sub (allocate Ψ w) _ _
lemma candle (h:SatP μ K F H A)(hv: SatP μ Y F H A): Cabin A (K-Y) μ F H= Cabin A K μ F H-Cabin A Y μ F H:= by
    funext w; unfold Cabin; have he (i j:BH G)(l r:Legs (Lane4 G))(q:QP): meshZ (K-Y) i j F H l r q= meshZ K i j F H l r q - meshZ Y i j F H l r q:= by simp [meshZ,mul_sub,sub_mul]
    rw [Pi.sub_apply]; simp_rw [he,mul_sub,integral_sub (h ..) (hv ..), Finset.sum_sub_distrib,mul_sub]; exact map_sub (allocate Ψ w) _ _
lemma willow (hK: SatC μ K F b)(hw:Course b w)(he: SatC μ Y H b)(hF:SatC μ K H b): cycle K μ F w-cycle Y μ H w=cycle ( K-Y ) μ H w+ cycle K μ (F-H) w:= by rw [of_subc hK hF hw, other_subc hF he hw]; ring
-- at each rank without Estimate. Duhamel recurrence. use root operator equality LinearMap.
lemma twirlT (u a b:Law G)(K L:Edge G)(c:Law G): tree parity K u a-tree parity L c b= tree parity ( K-L ) c b+ tree parity K (u-c) b+ tree parity K u (a-b):= by
   funext i; let P:=allocate Ψ i (R:=ℂ); unfold tree; simp only [Pi.add_apply, Pi.sub_apply]; change P _-P _=P _+P _+P _; rw [← map_add,← map_add,← map_sub]; congr! 1; ext l r; simp only [attaches,Pi.add_apply,Pi.sub_apply,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; ring
lemma wirth (h: SatP μ K F H A)(hp: SatP μ K F W A)(hv: SatP μ K U W A)(hy:SatP μ Y U W A): Cabin A K μ F H-Cabin A Y μ U W= Cabin A K μ F (H-W)+Cabin A K μ (F-U) W+Cabin A ( K-Y ) μ U W:= by rw [sift hp hv, candle hv hy,sift' h hp]; abel
-- size. rank≤ powers.Support caps
lemma capcy (h:Limit F s)(K:Edge G)(μ:Measure QP): Limit (cycle K μ F) (s-2):= by
   intro l hl; unfold cycle; simp_rw [at_trc,show ∀ (i j:Lane4 G),F (i::j::l)=0 from fun i j=> h _ (by simp; omega) ]; simp
lemma capjoin (h:Limit F s)(ht:Limit H r)(μ:Measure QP)(K: Edge G)(A:QP): Limit (Cabin A K μ F H) (s+r-2):= by
   intro l hl; unfold Cabin; rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..);
   intro x y hh; obtain he:= split_length hh; by_cases hm:(x.length:ℤ)+1>s; · simp_rw [meshZ,show ∀ i:Lane4 G,F (i::x)=0 from fun _=> h _ (by simp; omega) ]; simp
   simp_rw [meshZ,show ∀ i:Lane4 G,H (i::y)=0 from fun _=> ht _ (by simp; omega)]; simp
lemma leastT (h:Limit F s)(hp:Limit H r)(K:Edge G): Limit (tree parity K F H) (s+r-2) := Wind.Modeled.guard h hp _
section
variable {ι:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {X Y:ι→Law G}{K:ι→Edge G}{a b' z x y:ι→ℝ}{μ:ι→Measure QP}{S:Scale ι}{d:ℕ}{A:ι→QP}
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma add_split (u v:Legs E): Split u v (u++v):= by induction u with| nil=> (change Split [] v v; induction v with| nil=> exact .nil| cons i v ih=> exact .right ih)| cons i u ih=> exact .left ih
lemma herec (h:glob S μ d)(hk:Sheet S a K)(hu:Lease b true S X x)(ha:nn a)(hx:nn x)(i:ι): SatC (μ i) (K i) (X i) b:= by
    intro l hl; obtain he:= Rapid.integrates h ( topCycle hu hk ( ray_course hl ) hx ha) i (1:ℝ); simpa only [ray_sail] using he
lemma priceP (he:Sheet S a K)(hx:Lease false true S X x)(hy: Lease false true S Y y)(h:glob S μ d)(i:ι) (A:QP): SatP (μ i) (K i) (X i) (Y i) A:= by
    intro u v k l; have H:=meshC he u v (add_split (ray k) (ray l)) hx hy; simpa only [ packMesh, ray_sail ] using ( rayTag (fun _:ι=> sailor A) h H i).values (1:ℝ)
end
end YM.MS.Latch

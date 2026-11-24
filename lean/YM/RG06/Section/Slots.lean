import YM.RG06.Weak.Price
import YM.RG06.Weak.Shift
import YM.Bid.Source
/-!
# The based transported curvature slots used by `Bid.pop`

All orders from oriented path plates. Slots on Cover, even when
sampled on a (wrapped) torus. `linear_slot` identifies the constant
coefficient of a divided slot as the exterior cochain loop sum around
the indicated PLAQUETTE; the connecting path does not appear in the
free leading coefficient. `access` in Drops.lean uses exactly the
continuum chord integrals of the smoothed radial potential used in
classical projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Section
open RG06 Weak Lattice Pert Function RG Source Drops Wilson
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

local notation "V"=> RG.Slot × G.ColorIndex

section linear
variable {S : Type*} [Semiring S]
lemma meet₀(F H:ℕ→S): Weak.join F H 0=F 0*H 0:=by simp [Weak.join_range]
lemma meet₁(F H:ℕ→S): Weak.join F H 1=F 0*H 1+F 1*H 0:=by
  rw [Weak.join_range,Finset.sum_range_succ,Finset.sum_range_one]

lemma flip_zero (A:G.Color)(s:Bool):turn s (Weak.letter A) 0=1:=by cases s <;>simp [turn,Weak.letter,back]
lemma flip_one (A:G.Color)(s:Bool):turn s (Weak.letter A) 1= G.colorMat (if s then -A else A) :=by cases s <;> simp [turn,Weak.letter,back,G.colorMat_skew]
variable {R : Type*}[AddCommGroup R][One R]
lemma cycle_zero (a:Links R G.Color)(x:Four R)(k:Walk):cycle a x k 0=1:=by
 induction k generalizing x with
 | nil=>rfl
 | cons d k ih=> exact meet₀ .. |>.trans <| by rw [show turn d.neg (tile a _) 0=_ from flip_zero (a _) _, show cycleWith (tile a) (x+d.vec) k 0=1 from ih _,mul_one]

lemma line_walk (a:Links R G.Color)(x:Four R)(k:Walk): cycle a x k 1= G.colorMat (Exterior.linkSum a x k):=by
 induction k generalizing x with
 | nil=> change 0=G.colorMat 0; exact G.colorMat.map_zero.symm
 | cons d k ih=>
   change join (turn d.neg (letter (a _))) (cycle a _ k) 1 = _
   rw [meet₁, Exterior.linkSum,map_add,flip_zero,flip_one,one_mul, cycle_zero,mul_one,ih,add_comm]

lemma skew_linear (a:G.Color): Pert.First.recoverL G (G.colorMat a)=a:=by
 change G.projectColor ((1/2:ℝ) • (G.colorMat a-star (G.colorMat a)))=a
 rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ,smul_smul]; norm_num

lemma plate_zero (x:Four R)(a:Links R G.Color)(k:Walk)(i j : Axis) : plateSeries (tile a) x k i j 0=0:=by
  simp only [plateSeries,transport,skew,comp_apply,meet₀, back]
  simp only [show cycleWith (tile a)=cycle a from rfl,cycle_zero,recover_one,map_zero,mul_zero,zero_mul]

lemma plate_one (x:Four R)(a:Links R G.Color)(k:Walk)(i j : Axis) : plateSeries (tile a) x k i j 1 = Exterior.linkSum a (stop x k) (square i j):=by
  simp only [plateSeries,transport,skew,comp_apply,meet₁, meet₀,back, show cycleWith (tile a)=cycle a from rfl,cycle_zero,line_walk,skew_linear,recover_one,map_zero,mul_zero,zero_mul,star_one,
    mul_one,one_mul,G.project_colorMat, add_zero,zero_add]
end linear

def slotSeries (F:Links ℤ (ℕ→G.Mat))(S:RG.Slot): ℕ→ G.Color:=plateSeries F 0 S.walk S.plaq.val.1 S.plaq.val.2

theorem honest {f:ℝ→CoverConfig G} {F:Links ℤ (ℕ→G.Mat)} (h:Weak.tiled f F) (S:RG.Slot): Weak.Writes (S.eval ∘ f) (slotSeries F S) := plateSeries_honest h ..

def realLetter (a:Links ℤ G.Color)(i:V):ℕ→ℂ:= fun n=> (↑(slotSeries (tile a) i.1 n i.2):ℂ)

lemma chart_rule (a:Links ℤ G.Color)(i:V):Writes (fun t:ℝ=> (↑(i.1.eval (ray a t) i.2):ℂ)) (realLetter a i):= (honest (ray_tiled a) i.1).apply (Complex.ofRealCLM.comp (EuclideanSpace.proj i.2))

def curvedSlot (a:Links ℤ G.Color)(i:V): PowerSeries ℂ:= Weak.peel (realLetter a i)

theorem divided (a:Links ℤ G.Color)(i:V): Weak.DeSlot 1 (fun t:ℝ=> (↑(i.1.eval (ray a t) i.2):ℂ)) (curvedSlot a i):= by
  have he:=chart_rule a i; refine Weak.peel_slot he <| he.origin.symm.trans ?_
  unfold realLetter slotSeries; rw [plate_zero]; change ((0:ℝ):ℂ)=0; exact Complex.ofReal_zero

def linearSlot (a:Links ℤ G.Color)(i:V):ℂ:= ↑(Exterior.linkSum a i.1.offset (square i.1.plaq.val.1 i.1.plaq.val.2) i.2)

/-- Least power of the stencil (the free curvature data). -/
theorem linear_slot (a:Links ℤ G.Color)(i:V) : PowerSeries.constantCoeff (curvedSlot a i)= linearSlot a i:=by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,curvedSlot,peel,PowerSeries.coeff_mk]; unfold realLetter slotSeries; rw [plate_one]; rfl

theorem chord {d:ℕ}(p:Snap G d)(i:V): PowerSeries.constantCoeff (curvedSlot (access p) i)= (↑(Drops.glow p i.1 i.2):ℂ):=linear_slot ..

def sheet (S:RG.Slot) := Weak.inventory (0:Cover) S.walk ++ Weak.inventory S.offset (square S.plaq.val.1 S.plaq.val.2)

@[simp] lemma sheet_length (S:RG.Slot): (sheet S).length=S.length:=by rw [sheet,List.length_append,Weak.inventory_length,Weak.inventory_length,RG.Slot.length];rfl

theorem slot_bound (a:Links ℤ G.Color) (r:ℝ) (hr:0 ≤ r)(i:V)(h:∀ v∈sheet i.1,G.colorScale * ‖a v.1‖ ≤ r)(k:ℕ) :
    ‖PowerSeries.coeff k (curvedSlot a i)‖ ≤ Weak.weight (r*(2*i.1.walk.length+4:ℕ)) (k+1)/G.colorScale:=by
  obtain ⟨S,c⟩:=i
  rw [curvedSlot,Weak.peel,PowerSeries.coeff_mk]; unfold realLetter slotSeries
  have e := Weak.cost_plate a (0:Cover) S.walk S.plaq.val.1 S.plaq.val.2 hr (fun i hi=> h i (by simp [sheet,hi])) (fun i hi=>h i (by unfold sheet; apply List.mem_append_right _ hi)) (k+1)
  exact le_trans (by
    rw [Complex.norm_real,Real.norm_eq_abs]; change |(plateSeries (tile a) (0:Cover) S.walk S.plaq.val.1 S.plaq.val.2 _ : G.Color) c| ≤ _
    let w : G.Color:= plateSeries (tile a) (0:Cover) S.walk S.plaq.val.1 S.plaq.val.2 (k+1)
    simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ c) w) e

end YM.RG06.Section

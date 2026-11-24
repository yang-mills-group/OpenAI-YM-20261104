import YM.SchemeConversionRG11.FirstW.Calx.Loom
/-! Locally converging smooth shell bill. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent
open scoped BigOperators Classical ContDiff
variable {T:Itinerary}{G:Gauge}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {p:ℕ → Field4 G} {f:ℕ → Cover→ E} {W E': Set E4}{a b :ℤ}
lemma SlipM (u:Step) (h:∀ i:Axis,Melody T W a (fun j x=>up i (f j) x)) : Melody T W a (fun j x=> f j (x+u.vec)-f j x) := by
 rcases u with ⟨i,p|p⟩
 · exact h _
 let v:Cover:= -step i
 have H(j:ℕ)(x:Cover): f j (x+v)- f j x=(-1:ℝ) • up i (f j) (x+v):=by simp [up,v,add_assoc]
 change Melody T W a (fun j x=> f j (x+v)-_); simp_rw [H]; exact ((h i).drift v).fixed _
lemma BeadS (i:Step)(h:∀ s:Axis,Melody T W a (fun j x=> p j (x,s))): Melody T W a (fun j x=>boardAt x i (p j)) := by simp_rw [board_spin]; exact ((h i.dir).drift _).fixed _
lemma rail_m (i j:Step)(h: Deaf T W a p): Melody T W (a-1) (fun v x=> rail x (icon i j) (p v)):= by
 have hs(s t:Step) : Melody T W (a-1) (fun v x=>boardAt (x+t.vec) s (p v)-boardAt x s (p v)) := by
    simp_rw [board_spin,← smul_sub]
    have hp:=SlipM (f:=fun i=>field4 s.dir (p i)) t (h.loft _); simp_rw [add_right_comm _ t.vec (torMark s)]; exact Melody.fixed (hp.drift _) _
 simp_rw [close_read]; exact Melody.sub (hs j i) (hs i j)
-- χ differences along offset: any fixed, divide by h to get ray. use split ℤ or use real derivative.
lemma rise_tab (T:Itinerary)(Q:Wash)(x y:Cover): Melody T W (-1) (fun i v=>tabL T Q i (v+x)-tabL T Q i (v+y)):= by
 -- every x reachable. root plus diff. use existing Cover induction
 have hp (p:Cover): Melody T W (-1) (fun i v=>tabL T Q i (v+p)-tabL T Q i v):=by
   let f := tabL T Q
   have he : Melody T W (-1) (fun i v=> f i (v+0)-f i v):=by simp only [add_zero,sub_self]; exact Melody.zero
   have ht (p:Cover)(H : Melody T W (-1) (fun i v=>f i (v+p)-f i v))(s:Step): Melody T W (-1) (fun i v=> f i (v+(p+s.vec))-f i v):=by
     have h : Melody T W (-1) (fun i v=> f i (v+s.vec)-f i v):=by
       refine SlipM (f:=f) _ (fun i=>?_)
       refine ⟨costR [i] (soft Q),fun σ hs z hz p hp=>?_⟩
       have hh:= rolling [i] (soft Q) (soft_price Q) (Rig.path T σ hs).positive (Rig.path T σ hs).cutoff hp; apply hh.congr; intro j
       simp only [ped,f,up,lens,nudgeR,smul_eq_mul,tabL,Moss,inc_add,inc_step,zpow_neg_one]; rfl
     refine Eq.mp ?_ (Melody.add (h.drift p) H); simp_rw [sub_add_sub_cancel,add_assoc]
   let e:= fun p:Cover=> Melody T W (-1) (fun i v=>f i (v+p)-f i v)
   have hm (w:Walk)(u:Cover)(hu:e u):e (stop u w):= by induction w generalizing u with| nil=> exact hu| cons i w ih=> exact ih _ (ht u hu i)
   have h:=hm (route 0 p 1) 0 he; rw [route_end] at h; exact h
 have h:= (hp x).sub (hp y); convert! h using 1; simp only [sub_sub_sub_cancel_right]
-- error cost of gradient IBP data
variable {e : Cover→ G.Color} {k:ℕ}
def scar (Q:Wash)(T:Itinerary)(w:Walk) (p : ℕ→Field4 G)(i:ℕ)(x:Cover) := rail x w (windM T Q i (p i))- soft Q (Moss T i x) • rail x w (p i)
-- triangular recursion on shifted starting point
lemma scar_value (Q:Wash)(p:ℕ→Field4 G) (T:Itinerary)(i)(x y:Cover)(s:Step): boardAt (x+y) s (windM T Q i (p i))= tabL T Q i (x+(y+torMark s)) • boardAt (x+y) s (p i):=by rw [board_spin,board_spin]; unfold windM; rw [← add_assoc, smul_comm]
lemma scar_lands (Q:Wash)(w:Walk)(h:∀ a':Axis, Melody T W a (fun i x=>p i (x,a'))): Melody T W (a-1) (scar Q T w p):=by
 have ht (y:Cover): Melody T W (a-1) (fun i x=>rail (x+y) w (windM T Q i (p i))- tabL T Q i x • rail (x+y) w (p i)):=by
   induction w generalizing y with
   | nil=> simp only [rail,LinearMap.zero_apply,smul_zero,sub_zero]; exact Melody.zero
   | cons u w ih=>
     simp only [rail,LinearMap.add_apply,smul_add,add_sub_add_comm, ← sub_smul,scar_value,add_assoc]; refine Melody.add ?_ (ih (y+u.vec)); have he:=rise_tab (W:=W) T Q (y+torMark u) 0; simp_rw [add_zero] at he; rw [show a-1=-1+a by omega]
     let L : ℝ→L[ℝ] G.Color →L[ℝ] G.Color:= (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ G.Color)
     exact Melody.linked he ((BeadS u h).drift y) L
 simpa only [add_zero] using! ht 0
lemma Melody.inside (h:Melody T W a f)(hp:E'⊆W): Melody T E' a f := by obtain ⟨g,h⟩:=h; exact ⟨g,fun σ hs v hv p he=> h σ hs v (hp hv) p he⟩
lemma smock_step (k:ℕ)(p:ℕ→Field4 G)(h:∀ s:Axis, Melody T W a (fun i x=>p i (x,s)))(u:Cover→ G.Color)(he:u∈Loft _ k)(s:Axis) : Melody T W (a+k) (fun i x=>shiftT u (p i) (x,s)):=by
 obtain ⟨L,hL⟩:= doubles G.ad; simp only [shiftT,LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.proj_apply,← hL]; have hp : Melody T W (k:ℤ) (fun _=> u):= (figK k u he).inside (subset_univ _); rw [add_comm]; exact Melody.fixed (Melody.linked (hp.add (hp.drift (step s))) (h s) L) _ -- scale? LinearMap.smul_apply
end YM.RG11.FirstW

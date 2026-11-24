import YM.GapsContact.Tube.Scale

/-! Isometric Wick coordinates for a real configuration of any finite arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedTubeCoordinates
open Function Set Boundary Boundary.Surface GapsContact GapsContact.Tunnel
open scoped Topology Classical
variable {n : ℕ}

def plane (x : SpacePoints n) (y : Heights n) : Full n :=
  glow (place x (0 : Heights n)) (dawn y)

private lemma place_ray {n : ℕ} (t : ℝ) (x u : SpacePoints n) (y w : Heights n) :
    place (x+t • u) (y+t • w) = place x y+t • place u w := by
  apply PiLp.ext; intro j
  apply Mink.ext_by <;> simp [place,smul_eq_mul]

theorem plane_ray (t : ℝ) (x u : SpacePoints n) (y w : Heights n) :
    plane (x+t • u) (y+t • w) = plane x y+(t:ℂ) • plane u w := by
  have hx : place (x+t • u) (0 : Heights n) = place x 0+t • place u 0 := by
    simpa only [smul_zero,add_zero] using place_ray t x u (0 : Heights n) 0
  have hy : dawn (y+t • w) = dawn y+t • dawn w := by
    simpa only [dawn,smul_zero,add_zero] using place_ray t (0 : SpacePoints n) 0 y w
  unfold plane
  rw [hx,hy]
  ext1 a
  simp [glow]
  ring

private lemma origin : plane (n:=n) 0 0 = 0 := by
  have e : plane (n:=n) 0 0 = plane 0 0 + plane 0 0 := by
    simpa only [one_smul,Complex.ofReal_one,add_zero] using
      plane_ray 1 (0 : SpacePoints n) 0 0 0
  calc plane 0 0 = (plane 0 0+plane 0 0)-plane 0 0 := by abel
       _ = 0 := by rw [←e,sub_self]

def embedding : (SpacePoints n × Heights n) →L[ℝ] Full n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p : SpacePoints n × Heights n => plane p.1 p.2
    map_add' := fun p q=>by
      simpa only [Prod.fst_add,Prod.snd_add,one_smul,Complex.ofReal_one] using
        (plane_ray (n:=n) 1 p.1 q.1 p.2 q.2)
    map_smul' := fun r p=>by
      change plane (r • p.1) (r • p.2) = r • plane p.1 p.2
      simpa only [zero_add,origin,Complex.coe_smul] using
        plane_ray r 0 p.1 0 p.2 }

private def profile (q : Points n) : SpacePoints n × Heights n := (trace q,fun i=>YM.time (q i))

private lemma profile_add (p q : Points n) : profile (p+q)=profile p+profile q := by
  apply Prod.ext
  · exact funext fun i=>Mink.rest_add (p i) (q i)
  · exact funext fun i=>Mink.clock_add (p i) (q i)

private lemma profile_smul (r : ℝ) (p : Points n) : profile (r • p) = r • profile p := by
  apply Prod.ext
  · exact funext fun i=>Mink.rest_mul (p i) r
  · exact funext fun i=>Mink.clock_mul (p i) r

private def profileLinear : Points n →ₗ[ℝ] SpacePoints n × Heights n where
  toFun := profile
  map_add' := profile_add
  map_smul' := profile_smul

private theorem profile_cont : Continuous (profile (n:=n)) := by
  apply Continuous.prodMk
  · exact continuous_pi fun i=>Mink.rest_cont.comp (PiLp.continuous_apply 2 _ i)
  · exact continuous_pi fun i=>Mink.clock_cont.comp (PiLp.continuous_apply 2 _ i)

def coordinates : Points n →L[ℝ] SpacePoints n × Heights n where
  toLinearMap := profileLinear
  cont := profile_cont

private lemma coordinate_price (q : Points n) (i : Fin n) (a : Axis) :
    ‖embedding (coordinates q) (i,a)‖=‖q i a‖ := by
  refine Fin.lastCases ?_ (fun k=>?_) a
  · change ‖(↑(YM.time (position (spatial (q i)) 0)):ℂ)+(↑(YM.time (position 0 (YM.time (q i)))):ℂ)*Complex.I‖=‖YM.time (q i)‖
    simp
  · change ‖(↑(spatial (position (spatial (q i)) 0) k):ℂ)+(↑(spatial (position 0 (YM.time (q i))) k):ℂ)*Complex.I‖=‖spatial (q i) k‖
    simp

theorem isometry (q : Points n) : ‖embedding (coordinates q)‖=‖q‖ := by
  rw [←Points.flatten.norm_map q,EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  rintro ⟨i,a⟩ -
  rw [coordinate_price,Points.flatten_at]

theorem rebuild (q : Points n) : place (coordinates q).1 (coordinates q).2 = q := by
  apply PiLp.ext; intro i
  exact position_eta (q i)

theorem straight (q u : Points n) (t : ℝ) :
    place ((coordinates q).1+t • (coordinates u).1) ((coordinates q).2+t • (coordinates u).2) = q+t • u := by
  have e := rebuild (q+t • u)
  rw [map_add,map_smul] at e
  exact e

theorem place_mul {n : ℕ} (r : ℝ) (x : SpacePoints n) (y : Heights n) :
    place (r • x) (r • y) = r • place x y := by
  apply PiLp.ext
  intro j
  apply Mink.ext_by <;> simp [place,smul_eq_mul]

theorem plane_inside (x : SpacePoints n) {y : Heights n} (hy : y∈east n) :
    plane x y ∈ tube n := by
  change shade (glow _ (dawn y)) ∈ fields n
  simpa only [im_glow] using etched hy

theorem plane_mul (r : ℝ) (x : SpacePoints n) (y : Heights n) :
    plane (r • x) (r • y) = (r:ℂ) • plane x y := by
  unfold plane
  rw [Room.dawn_mul,←glow_scales]
  congr 1
  simpa only [smul_zero] using place_mul r x (0 : Heights n)

end YM.Integration.WilsonSeparatedTubeCoordinates

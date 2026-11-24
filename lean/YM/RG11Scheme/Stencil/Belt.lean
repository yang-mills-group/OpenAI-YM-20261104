import YM.RG11Scheme.Stencil.Variation
import YM.RG11Scheme.Stencil.Gates

/-! Change of scale and origin exactly, before frame renormalization, including arguments of completion vertices crossing the quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 7000
set_option maxHeartbeats 135000
namespace YM.RG11Scheme.Stencil.Cell
open Filter Function Set Lattice Mesh Pert Spark Bare
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G:Gauge}{X:Type}[AddCommGroup X][One X] {j k : ℕ} {n:Side}
local notation "Δ" => Spark.tensor X G
lemma full2_flip (h:ℝ)(A B:Δ)(x:Four X) : full2 h x j B A= full2 h x j A B := by
   have he (l:Four X)(i k:Axis)(τ:Walk) (Y Z:Δ) : twin τ (l:Four X) i k Y Z=twin τ l i k Z Y := by simp_rw [twin_one]; rw [dflip]; abel
   have eq (s:Signed) : expander j (affine s⁻¹ 0 x) (wideLink G s B) (wideLink G s A)= expander j (affine s⁻¹ 0 x) (wideLink G s A) (wideLink G s B) := by
      funext i k γ; simp_rw [active]; congr 1; apply Finset.sum_congr rfl; intro l _ ; rw [he _ _ _ _ (wideLink G s B) (wideLink G s A)]
   simp_rw [rung, eq]

def pan (y:Four X) (A:Δ) : Δ := fun z=>A (z.1+y,z.2)
lemma drift (τ:Walk)(x y:Four X)(U:Lattice.Links X G.El)(i j) : plateU (translate y U) x τ i j=plateU U (x+y) τ i j := by
   have ht (s l) : travel (translate y U) l s=travel U (l+y) s := by simpa only [←pull_one,affine,Signed.act_one,Step.rotate_one, show List.map (fun x=>x) s=s from List.map_id ..] using (travel_pull s U 1 l y)
   have hx (x):stop (x+y) τ= stop x τ + y := by induction τ generalizing x with|nil=>rfl|cons a l ih=>rw [stop,stop,add_right_comm x,ih]
   unfold plateU; rw [ht,ht,hx x]
lemma swing (h:ℝ)(A:Δ)(x y:Four X): tensorJet h (ride (pan y A)) x j=tensorJet h (ride A) (x+y) j := by
   have hp (s:Signed) : pull s 0 (ride (pan y A))=translate (s⁻¹.act y) (pull s 0 (ride A)) := by
      rw [show ride (pan y A)=translate y (ride A) from rfl,←pull_one,←pull_one,pull_pull,pull_pull]; simp [affine]
   have hk (s:Signed): oval s h (ride (pan y A)) x j=oval s h (ride A) (x+y) j:=by
      unfold oval rawJet; rw [hp]; simp only [affine,add_zero,Signed.act_add, show ∀ a b u,diffU j (Lattice.translate b u) a=diffU j u (a+b) from fun a b (u:Lattice.Links X G.El)=> by funext i l z; simp only [diffU, drift]]
   unfold tensorJet; simp only [hk]

lemma wavelet (h:ℝ)(p:Scalar G j) (x y:Cover)(A:Bond G) : forward p (x+y) h A=forward p x h (pan y A) := by
   unfold forward; rw [LinearMap.comp_apply,LinearMap.comp_apply]
   apply congrArg; rw [←raw_one,←raw_one]
   refine congrArg (fun f:ℝ→Labels.Taylor G j=>iteratedDeriv 1 f 0) (funext fun t=> Eq.symm (swing h (t • A) x y))
lemma light (p:Scalar G j) (h:ℝ) (x y:Cover) (l:link) : ray (forward p (x+y) h) l = ray (forward p x h) (l.1-y,l.2) := by
   ext c; rw [ray_one,ray_one,wavelet]; apply congrArg; funext w
   unfold pan node; rw [show w.1+y-l.1=w.1-(l.1-y) by abel]

lemma signal (h:ℝ)(x y:Four X)(A:Δ): full2 h x j (pan y A) (pan y A)=full2 h (x+y) j A A := by
   rw [←raw_squares,←raw_squares];exact congrArg (fun f:ℝ→Labels.Taylor G j=>iteratedDeriv 2 f 0) (funext fun t=> swing h (t • A) x y)
variable {D E Y:Type}[AddCommGroup D][Module ℝ D] [AddCommGroup E][Module ℝ E][AddCommGroup Y][Module ℝ Y]
theorem twins (Z:D→ E) (A:D→ₗ[ℝ] D→ₗ[ℝ] Y)(B:E→ₗ[ℝ] E→ₗ[ℝ] Y)(x y:D) (hZ:Z (x+y)=Z x+ Z y) (ha:A y x=A x y)(hb:B (Z y) (Z x)=B (Z x) (Z y))(hx:∀ x:D,A x x=B (Z x) (Z x)):
   A x y=B (Z x) (Z y) := by
    have hm := hx (x+y)
    rw [hZ,map_add,map_add] at hm; simp only [LinearMap.add_apply, map_add, hx,ha,hb,add_assoc,add_right_inj] at hm
    have he : (2:ℝ) • (A x y-B (Z x) (Z y))=0 := by rw [smul_sub,sub_eq_zero,two_smul,two_smul]; simp only [← add_assoc] at hm; exact add_right_cancel hm
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (by norm_num))
lemma corona (h:ℝ)(p:Scalar G j)(x y:Cover) (A B:Bond G) : cross p (x+y) h A B= cross p x h (pan y A) (pan y B) := by
   have fl (A B:Bond G) (x:Cover): cross p x h B A=cross p x h A B := by rw [cross,LinearMap.compr₂_apply,LinearMap.compr₂_apply,full2_flip]
   have hp (z: Bond G): cross p (x+y) h z z=cross p x h (pan y z) (pan y z):= by unfold cross; simp only [LinearMap.compr₂_apply,signal]
   have ho : pan y (A+B)=pan y A+pan y B:=funext fun _=>rfl
   have he := twins (Y:=ℝ) (E:=Bond G) (D:=Bond G) (pan y) (cross p (x+y) h) (cross p x h) A B ho (fl A B (x+y)) (fl (pan y A) (pan y B) x) hp
   with_reducible exact he
lemma outside_scale (h:ℝ)(s:Signed)(A:Response G j) : outside h s j A= (h^(j+2))⁻¹ • outside 1 s j A := by
   unfold outside; rw [LinearMap.comp_apply,LinearMap.comp_apply, LinearMap.smul_apply,map_smul]; simp only [one_zpow,one_smul]; rw [show h^(-(j+2:ℤ))=(h^(j+2))⁻¹ by rw [zpow_neg, ← Nat.cast_ofNat (n:=2) (R:=ℤ), ←Nat.cast_add, zpow_natCast]]
lemma clear_scale (h:ℝ)(x:Cover)(p:Scalar G j) : forward p x h = (h^(j+2))⁻¹ • forward p x 1 := by
   apply LinearMap.ext; intro A
   have he : wideLinear G j h x A=(h^(j+2))⁻¹ • wideLinear G j 1 x A := by rw [sided,sided]; simp_rw [outside_scale h, ← Finset.smul_sum]; rw [smul_comm]
   rw [LinearMap.smul_apply,forward,forward,LinearMap.comp_apply,LinearMap.comp_apply,he,map_smul]
lemma cross_flip (h:ℝ)(x:Cover)(p:Scalar G j) (A B:Bond G): cross p x h A B=cross p x h B A := by rw [cross,LinearMap.compr₂_apply,LinearMap.compr₂_apply,full2_flip]
lemma cross_scale (h:ℝ)(x:Cover)(p:Scalar G j)(A B:Bond G) : cross p x h A B= (h^(j+2))⁻¹ * cross p x 1 A B := by
   have he : full2 h x j A B=(h^(j+2))⁻¹ • full2 1 x j A B := by rw [rung,rung]; simp_rw [outside_scale h, ← Finset.smul_sum]; rw [smul_comm]
   rw [cross,cross,LinearMap.compr₂_apply,LinearMap.compr₂_apply,he,map_smul]; rfl
end YM.RG11Scheme.Stencil.Cell

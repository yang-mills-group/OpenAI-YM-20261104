import YM.PertExtension.ImageCost

/-! Scaled free-leaf comparison: separate unwrapped distant endpoint and reflected
image; as yet the diagram statement is for individual curvature letters, not a
quotient resolution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.PertExtension.LatticePT
namespace Projection
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall
open Next.Rank.Beamer Air Band Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge}

private def tune (u:ℝ) := Complex.exp ((2*π:ℝ)*Complex.I*u)-1
def band (r:ℝ) : Set ℝ:={u| r≤ |u|∧ |u|≤1-r}
lemma phase_large {r:ℝ} (h : 0<r) : ∃ δ>0,∀ u:ℝ,u∈band r→δ≤‖tune u‖ := by
    let X:=band r; by_cases hX:X.Nonempty; swap
    · exact ⟨1,zero_lt_one,fun u hu=> (hX ⟨u,hu⟩).elim⟩
    have hc : IsCompact X := IsCompact.of_isClosed_subset (isCompact_Icc (a:= -(1-r)) (b:=1-r)) (IsClosed.inter (isClosed_le continuous_const continuous_abs) (isClosed_le continuous_abs continuous_const)) (fun x hx=>abs_le.mp hx.2)
    have hn u (hu:u∈X) : 0 < ‖tune u‖:=by
      apply norm_pos_iff.mpr; rw [tune]; intro eh; obtain ⟨n,he⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp eh)
      push_cast at he
      have hp : ((2*π*Complex.I:ℂ))≠0:=by rw [show (2*π:ℂ) = ((2*π:ℝ):ℂ) by push_cast;rfl]; apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))) Complex.I_ne_zero
      have hb : (u:ℂ)=n := mul_left_cancel₀ hp (he.trans (mul_comm ..))
      apply_fun Complex.re at hb; norm_cast at hb
      have ha : |(n:ℝ)| < 1:= by rw [← hb]; linarith only [hu.2,h]
      have h₀:n=0:=by
         have hu₁: -1<n:=by exact_mod_cast (abs_lt.mp ha).1
         have hu₂:n<1:=by exact_mod_cast (abs_lt.mp ha).2
         omega
      have hx:r≤(0:ℝ):=(by simpa [hb,h₀] using hu.1);exact h.not_ge hx
    have he : ContinuousOn (fun u=>‖tune u‖) X:= ((Complex.continuous_exp.comp (continuous_const.mul Complex.ofRealCLM.continuous)).sub continuous_const).norm.continuousOn
    obtain ⟨u,hu,h'⟩:=hc.exists_isMinOn hX he
    exact ⟨_,hn u hu, h'⟩

lemma current_fee (n:Side)(i:Axis)(z:Cover): cwave n i (mapZ z)-1= tune ((z i:ℝ)/n.val):=by
  unfold cwave pebble tune;rw [←phase_matches, wrap_step,tone_unit]
  change ZMod.stdAddChar (N:=n.val) ((z i:Int):ZMod n.val)-_= _;rw [ZMod.stdAddChar_coe];push_cast;ring_nf

-- Full samples for colors in physical color basis, before image; all offsets lifted.
def stem (G : Gauge)(n: Side)(u : Cover)(i: Address G) : FaceAt n := (wrap n (u+i.1),i.2.1)
def lens (G : Gauge) (i : Address G) : Degree G:=⟨i.2.1,i.2.2,i.1,0,Fin.elim0⟩
def direct (G:Gauge)(n:Side)(u v:Cover):Bridge G:= fun i j=>(if i.2.2=j.2.2 then disk (shining (stem _ n v j)) (stem _ n u i) else 0).re
def reflected (G:Gauge)(n:Side)(u v:Cover):Bridge G:= fun i j=>(if i.2.2=j.2.2 then disk (shining (stem _ n v j)) (fold n (stem _ n u i)) else 0).re
lemma direct_price (a b:Degree G) (n) (u v x y:Cover): direct G n u v (x,a.a,a.paint) (y,b.a,b.paint)=(stepsP (shell a b) n 2 (captured u v x y)).re :=
   congr_arg Complex.re (plate_matches a b _ _ (u+x-(v+y)) rfl rfl ((wrap n).map_sub ..))

def reflectedOffset (u v x:Cover) (a:PlaqAxes)(y:Cover):= -((u+x)+(v+y))-step a.val.1-step a.val.2
lemma refwrap n u v x a y: (wrap n (reflectedOffset u v x a y)) = (fold n (wrap n (u+x),a)).1-wrap n (v+y):=by
    unfold reflectedOffset; rw [map_sub,map_sub,map_neg,map_add,wrap_step,wrap_step, fold];dsimp only; abel
lemma ref_price (a b:Degree G) (n) (u v x y:Cover): reflected G n u v (x,a.a,a.paint) (y,b.a,b.paint)=(stepsP (shell a b) n 2 (mapZ (reflectedOffset u v x a.a y))).re :=
   congr_arg Complex.re (plate_matches a b _ _ (reflectedOffset u v x a.a y) rfl rfl (refwrap ..))

-- TK applied at direct argument at arbitrary positive derivative orders
lemma directions (a b:Degree G)(k :ℕ) : ∃ C:ℝ, 0≤C ∧
    (Mist (parade a b (shell a b) - HeatP 1 a b) (a.degree+b.degree) C ∧ Lip (parade a b (shell a b)) 2 C) ∧ ∀ n (z:E4),
     1≤‖z‖→ ‖(stepsP (parade a b (shell a b)) n 2 z).re-Prayer.gleam a b z‖ ≤ C*stature (a.degree+b.degree) z (n.val:ℝ):=by
    let F:= shell a b; let D:=a.degree+b.degree+6; obtain ⟨c,hp⟩:= profile a b D
    let B:=max 1 c; have hb:1≤B:=le_max_left ..;have hC:c≤B:=le_max_right ..
    have he:Window F 2 B D 1 a b:=⟨hp.nonneg.trans hC,hp.event,hp.coast.trans hC,hp.meas,hp.cast.coin hC,hp.crest.coin hC⟩
    obtain ⟨u,hu,hU⟩:=intended 2 (by decide) a b (zero_lt_one) D (le_refl D)
    let A:=B*u
    let C':=max A 1
    have h₀:C'≥A:=le_max_left ..
    obtain ⟨hr,hM,hF⟩:= hU F B C' hb he (le_max_left ..)
    obtain ⟨q,hq,hQ⟩:= TK a b 2 zero_lt_one
    let C:= C'+q*C'
    have h' : 0≤ C':=zero_le_one.trans (le_max_right ..)
    have hv : C'≤C:=le_add_of_nonneg_right (mul_nonneg hq h')
    refine ⟨C,h'.trans hv,⟨⟨hM.part,fun i he z hz hh=> (hM.jet i he z hz hh).trans (mul_le_mul_of_nonneg_right hv (by positivity)), fun i he z hz=>(hM.far i he z hz).trans (div_le_div_of_nonneg_right hv (by positivity))⟩,⟨hF.event,fun _=>(hF.norm _).trans hv,hF.direct,fun i hi=>(hF.works i hi).trans hv⟩⟩,fun n z hz=>(hQ (parade a b F) C' (le_max_right ..) hr hM hF n z hz).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h') (by unfold stature;positivity))⟩

end Projection
end YM.PertExtension.LatticePT
namespace YM.PertExtension.LatticePT.Projection
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall
open Next.Rank.Beamer Air Band Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge}

theorem direct_cost (a b:Degree G) : ∃ C≥0,∀ n (u v:Cover),
    let z:=captured u v a.point b.point
    1≤‖z‖→ ‖mourn (gesture a) (gesture b) (direct G n u v)-Prayer.gleam a b z‖ ≤ C*stature (a.degree+b.degree) z n.val :=by
   obtain ⟨C,hC,_,h⟩:=directions a b 0
   refine ⟨C,hC,fun n u v hz=> ?_⟩ -- let intros
   rw [seats (H:=G) u v a b n 2 (shell a b) (direct G n u v) (direct_price a b n u v)] -- lambda
   exact h n (captured u v a.point b.point) hz
-- dominate image at individual spacings only, since arbitrary fixed inverse powers still covered

def basic (G : Gauge) (a:PlaqAxes) (j:G.ColorIndex) : Degree G:=⟨a,j,0,0,Fin.elim0⟩
theorem band_window (x y:PlaqAxes × G.ColorIndex) : ∃ C≥(0:ℝ),
 Lip (shell (basic G x.1 x.2) (basic G y.1 y.2)) 2 C:=by
  obtain ⟨C,h,h'⟩:=directions (basic G x.1 x.2) (basic G y.1 y.2) 1
  let X:=shell (basic G x.1 x.2) (basic G y.1 y.2)
  have he:= h'.1.2
  refine ⟨C,h,?_⟩
  convert! he using 1
  ext1 i
  simp only [parade, fling]
  simp [basic, X]

def Screen (r : ℝ) (n:Side) (i:Cover):=∃ j:Axis, ((i j:ℤ):ℝ) / n.val ∈ band r
lemma image_estimate {r}(hr:0<r) (G : Gauge):∃ C≥(0:ℝ),∀ n:Side,∀ i:Cover, Screen r n i→∀ a b:PlaqAxes × G.ColorIndex,
   ‖stepsP (shell (basic G a.1 a.2) (basic G b.1 b.2)) n 2 (mapZ i)‖≤C/n.val:=by
   obtain ⟨δ,hδ,h⟩:= phase_large hr
   choose C hc hC using (band_window (G:=G))
   let U:ℝ:=∑ a,∑ b,|costImage| *(C a b)
   have h₁ a b :0≤ |costImage| * C a b:= mul_nonneg (by positivity) (hc a b)
   have hU:0≤U:=sum_nonneg fun i _=>sum_nonneg fun j _=> h₁ i j
   refine ⟨U/δ,div_nonneg hU hδ.le,?_⟩; rintro n i ⟨j,hj⟩ a b
   let F:=shell (basic G a.1 a.2) (basic G b.1 b.2);let T:=stepsP F n 2 (mapZ i)
   have he := wave_cost n j (mapZ i) (hC a b) (hc a b)
   have ht : eventP 2 (banded F (mapZ i)):=fun z hz=> by unfold banded F; rw [(hC a b|>.event z hz),mul_zero]
   rw [← Band.extend n ht] at he
   have hz :δ≤‖cwave n j (mapZ i)-1‖:= by rw [current_fee]; exact h _ hj
   change ‖cwave n j (mapZ i)-1‖*‖T‖ ≤ costImage * C a b / n.val at he
   apply le_of_mul_le_mul_left (a:=(δ:ℝ)) ?_ hδ
   have hm (q:PlaqAxes × G.ColorIndex):0≤ ∑ b,|costImage| * C q b:=sum_nonneg (fun v _=> h₁ q v)
   have hm:costImage * C a b ≤ U:= ((mul_le_mul_of_nonneg_right (le_abs_self _) (hc a b)).trans (single_le_sum (s:=Finset.univ) (fun v _=> h₁ a v) (mem_univ _))).trans (single_le_sum (s:=Finset.univ) (fun v _=> hm v) (mem_univ _))
   calc δ*‖_‖ ≤ ‖cwave n j (mapZ i)-1‖*‖T‖:=mul_le_mul_of_nonneg_right hz (norm_nonneg _)
        _ ≤ δ*(U/δ/n.val) := he.trans ((div_le_div_of_nonneg_right hm (by positivity)).trans_eq (by field_simp[hδ.ne']))

theorem image_point {r}(hr:0<r)(G:Gauge):∃ C≥0, ∀ n:Side,∀ u v x y:Cover,∀ a b:PlaqAxes × G.ColorIndex,
 Screen r n (reflectedOffset u v x a.1 y) → ‖reflected G n u v (x,a) (y,b)‖ ≤ C/n.val:= by
   obtain ⟨C,h,hb⟩:=image_estimate hr G
   refine ⟨C,h,?_⟩;rintro n u v x y ⟨a,i⟩ ⟨b,j⟩ h
   dsimp only at h
   let z':=reflectedOffset u v x a y
   let X:=stepsP (shell (basic G a i) (basic G b j)) n 2 (mapZ z')
   have he:reflected G n u v (x,a,i) (y,b,j)=X.re:=ref_price (basic G a i) (basic G b j) ..
   rw [he]
   exact (Complex.abs_re_le_norm _).trans (hb n (reflectedOffset u v x a y) h (a,i) (b,j))
end YM.PertExtension.LatticePT.Projection

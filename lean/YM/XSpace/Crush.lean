import YM.XSpace.Shadows

/-!
# Pressure and rotation terms of the local Ward identity

One harmonic leg even at full covering scale. Coordinate representation (G-adjoint).
The pressure cross contraction into an ordinary leg of a W0-pol collapses to stencil
support. Do not make continuum delta assumptions (lattice K identities suffice here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Prelude
open Function Set Filter Future Lattice Scale Sail Further.FreeCovariance.KP Drama Lows Mu Chart2 MvPolynomial Next.Rank.Normal Trace
open scoped Topology BigOperators InnerProductSpace ContDiff
variable {G:Gauge} {k:ℕ}
def curlFee (x:Cover)(i j:Axis)(c:G.ColorIndex):Fee G:= ⟨1,Trace.touch x i j [] c,touch_cane x i j [] c⟩
lemma curls_hit (x:Cover)(i j:Axis)(c:G.ColorIndex)(A:Contact G): probe (curlFee x i j c).line A=(crackle i j A x) c:= Trace.paid ..
def main (x:Cover)(j:Axis)(c:G.ColorIndex): Line G:= ∑ i:Axis, ((curlFee (x-step i) i j c).line - (curlFee x i j c).line)
def chassis (x:Cover)(j:Axis)(c:G.ColorIndex):=harp (main x j c)
lemma main_ap (x:Cover)(j:Axis)(c:G.ColorIndex)(A:Contact G): probe (main x j c) A=(Scale.press A (x,j)) c:=by
  unfold main; rw [map_sum,LinearMap.sum_apply,← fit_value _ (Scale.press A) j,Scale.job, Finset.sum_apply]; simp only [map_sub,LinearMap.sub_apply,curls_hit, WithLp.ofLp_sum,Finset.sum_apply]; rfl
abbrev nozzle (p:Cover)(j:Axis)(c:G.ColorIndex):UnitIndex G:=((p,j),c)
-- adjoint action on pol coordinates, with neighbor averaging required
abbrev Warp (G:Gauge):= Cover→G.Color
def layer (v:Warp G)(x:Cover)(j:Axis)(i b:G.ColorIndex):ℝ:= (rLink v (crumb ((x,j),b)) (x,j)) i
def pebble (x:Cover)(j:Axis)(i:G.ColorIndex)(v:G.Color)(b:G.ColorIndex):ℝ:=G.ad (basisC G b) v i
lemma layered (v:Warp G)(x:Cover)(j:Axis)(i b:G.ColorIndex):layer v x j i b=pebble x j i ((1/2:ℝ) • (v (x+step j)+v x)) b:= by rw [layer,r_at]; simp [crumb,pebble]
lemma pebble_zero (x:Cover)(j:Axis)(i:G.ColorIndex)(v:G.Color):pebble x j i v i=0:= by unfold pebble; rw [← EuclideanSpace.basisFun_inner]; rw [Drift.ad_swap,inner_neg_right, Drift.ad_e,neg_zero]
def rollLine (v:Warp G)(x:Cover)(j:Axis)(i:G.ColorIndex):Line G:=∑ b:G.ColorIndex,layer v x j i b • needle ((x,j),b)
lemma tollLine (v:Warp G)(x:Cover)(j:Axis)(i:G.ColorIndex)(A:Contact G):probe (rollLine v x j i) A= (rLink v A (x,j)) i:=by
  let S:=((1/2:ℝ) • (v (x+step j)+v x)); unfold rollLine; rw [map_sum, LinearMap.sum_apply,r_at]; conv_rhs=>rw [show A (x,j)=∑ b:G.ColorIndex, (A (x,j) b) • basisC G b from ((basisC G).sum_repr _).symm,map_sum]; skip
  simp only [map_smul,LinearMap.smul_apply,LinearMap.sum_apply,probes,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,ram_at]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; rw [layered]; unfold pebble; simp only [map_smul,PiLp.smul_apply,smul_eq_mul]; ring
lemma ink_curl (y:Cover)(i j:Axis)(c:G.ColorIndex){b:G.ColorIndex}(h:b≠c)(e:Edge Cover) : handshake (curlFee y i j c).line (needle (e,b))=0:=by
  have ht (x:Edge Cover): φ (G:=G) (e,b) x c=0:=by unfold φ; split_ifs; exact (color_equalizer ..).trans (if_neg h); rfl
  rw [handshake,baked,curls_hit,crackle_ap]; simp only [PiLp.sub_apply,ht,sub_self]
lemma neighbor_off (u:Line G)(x:Cover)(j:Axis)(c:G.ColorIndex)(v:Warp G)(h:∀ b:G.ColorIndex,b≠c → handshake u (needle ((x,j),b))=0) : handshake u (rollLine v x j c)=0:=by
  unfold rollLine handshake; rw [map_sum,map_sum]; apply Finset.sum_eq_zero; intro b _; by_cases he:b=c; subst b; rw [layered,pebble_zero,zero_smul,map_zero,map_zero]; simp only [map_smul]; change _ • handshake u _=_; rw [h b he,smul_zero]
lemma main_self (x:Cover)(j:Axis)(c:G.ColorIndex)(v:Warp G): handshake (main x j c) (rollLine v x j c)=0:=by
  apply neighbor_off; intro i hi; unfold main handshake; rw [map_sum,LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro k _; rw [map_sub,LinearMap.sub_apply]; exact sub_eq_zero.mpr ((ink_curl _ _ _ _ hi _).trans (ink_curl _ _ _ _ hi _).symm)
lemma price_legs (p q:Line G)(h:handshake p q=0): flicker (harp p*harp q)=harp p*harp q:=by rw [ripple,leg,show part (G:=G) _ (harp q)=C (handshake p q:ℂ) from (played q (bake p)).trans (congr_arg (fun c:ℝ=> C (σ:=UnitIndex G) (c:ℂ)) (listening q p)),h]; simp

def pulseR (v:Warp G)(x:Cover)(j:Axis)(i:G.ColorIndex):= harp (rollLine v x j i)
lemma pulse_at (v:Warp G)(x j i)(A:Contact G):pit A (pulseR v x j i)= (↑(rLink v A (x,j) i):ℂ):=by rw [pulseR,leg_test, tollLine]
lemma price_arm (x:Cover)(k j:Axis)(i:G.ColorIndex){b:G.ColorIndex}(h:b≠i)(v:Cover) : (freeze (harp (curlFee (x-step k) k j i).line *X ((v,j),b)))=harp (curlFee (x-step k) k j i).line * X ((v,j),b):=by rw [← harps (G:=G) ((v,j),b)]; apply no_twin; rw [gone,price_legs _ _ (ink_curl _ _ _ _ h _)]
lemma gauge_kills {p:Stamp G}{u w:Contact G}(h:p∈OnStage G k)(he:∀ x:Line G,Stops x→probe x u=probe x w): part u p=part w p:=by
  induction h using Submodule.span_induction with
  | mem p h=>
    obtain ⟨L,hL,rfl⟩:=h; have hh:=hL.2; clear hL
    induction L with
    | nil => simp only [steam]; change D u 1=D w 1; simp
    | cons i L ih=>rw [read_word]; change D u _=D w _; rw [(D u).leibniz,(D w).leibniz,played, played,he _ (hh i (by simp)),show D u (story L)=_ from ih (fun i h=> hh i (by simp [h]))]; rfl
  | zero=> simp
  | add=> simp_all only [map_add]
  | smul => simp_all only [map_smul]

lemma crushing (x:Cover)(j:Axis)(c:G.ColorIndex)(v:Warp G)(A:Contact G)(h:Scale.press A=0)(p:Stamp G)(H:p∈OnStage G k): pit A (tie G p (flicker (chassis x j c*pulseR v x j c)))=
    pit A (flicker (pulseR v x j c* part (G:=G) (crumb ((x,j),c)) (freeze p))):=by
  let u:UnitIndex G:=((x,j),c); let L:=main x j c; set R:= rollLine v x j c; rw [tie_ap,came,chassis, mul_comm (freeze p),mul_assoc,ripple,map_add,map_mul,leg_test, main_ap,h]; have hp : part (G:=G) (bake L) (freeze p)=part (G:=G) (crumb u) (freeze p):=by
    have he(z: Line G)(h:Stops z):probe z (bake L)=probe z (crumb u):=by
      rw [launched,← Trace.ticket, ← reverts z h]; exact (listening z L).trans (main_ap x j c _)
    rw [show part (G:=G) _ (freeze p)=_ from (slip (bake L) p).symm]; exact congr_arg freeze (gauge_kills H he) |>.trans (slip (crumb u) p)
  have h₀: (D (bake L)) (pulseR v x j c)=0:=by rw [pulseR,played]; change C ((↑(handshake R L)):ℂ)=_; rw [listening, main_self]; simp
  change (↑(0:ℝ):ℂ)*_+ pit A (flicker (D (bake L) (pulseR v x j c * freeze p)))=_; rw [(D (bake L)).leibniz, h₀,show D _ (freeze p)=_ from hp]; simp; rfl
end YM.XSpace.Prelude

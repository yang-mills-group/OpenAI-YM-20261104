import YM.MSbar.Chord.Fold
import YM.AnalyticNext.QUARTIC_MATCH.Local.Angles
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> n.val
local notation "t!"=> tint G (Exterior.Body 1 n)
noncomputable def curlX (s:Signed)(p:Face (Per n))(x:Positions (Primary n G)):= faceCurl p (Bid.pulled ((tint G _) x) s)
lemma rotated (s:Signed)(p:Face (Per n))(x:X) : curlX s p x=turned s p.2 • faceCurl (Face.send s 0 p) (tint G (Exterior.Body 1 n) x):=by
    let y:= tint G _ x; unfold curlX; ext i; have h := rotations_d (Exterior.parts G 1 y i) s p.1 p.2; rw [← pigment s n G y i] at h; exact h
lemma forwards (p:Face (Per n))(x:Positions (Primary n G)): let a := panel G n x; let i:=p.2.val.1; let b:=p.2.val.2; let y:=p.1
    faceCurl p (tint G _ x)= a (y+step i,b)-a (y,b)-(a (y+step b,i)-a (y,i)) :=by
    intro a i b y; ext c; exact Exterior.d_plaquettes y p.2 (Exterior.parts G 1 (tint G _ x) c) -- inspect args
-- closure linear compliance
noncomputable def basin (s:Signed)(k:Face (Per n)): Positions (Primary n G)→ₗ[ℝ]G.Color where
    toFun:= curlX s k
    map_add' x y:=by rw [rotated,forwards, rotated,forwards,rotated,forwards]; simp only [map_add,Pi.add_apply]; module
    map_smul' r x:= by rw [rotated,forwards, rotated,forwards]; simp only [map_smul,Pi.smul_apply,RingHom.id_apply]; module
noncomputable def tuner (e:G.Color)(x:Site n):=bead G (x,(1:Axis)) e
noncomputable def queue (e:G.Color)(n:Side)(f:Site n→ℝ):Positions (Primary n G) := ∑ i,f i • tuner e i
lemma tally (e:G.Color)(v:S₀→ℝ)(x:S₀)(a:Axis) : panel G n (queue e n v) (x,a) = if a=1 then v x • e else 0:=by
   unfold queue tuner; rw [map_sum]; simp_rw [map_smul,edges, Finset.sum_apply, Pi.smul_apply]; by_cases he:a=1
   · subst a; rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _),Pi.single_eq_same]; simp; exact fun j _ hx=>by simp [Pi.single_apply,Ne.symm hx,hx]
   rw [if_neg he]; exact Finset.sum_eq_zero fun j _=> by simp [Pi.single_apply,he]
-- orientation atom stencil.Support and costs
variable (s:Signed)(a:Face (Per n))(e:G.Color)
local notation "B"=> Face.send s 0 a
local notation "H"=>tint G (Exterior.Body 1 n)
local notation "K"=> tuner e
lemma even_price : ‖turned s a.2‖=1:=by unfold turned; dsimp only; split_ifs <;> norm_num
lemma readY(x:S₀):‖curlX s a (tuner e x)‖ ≤ 4*‖e‖:=by
    rw [rotated,norm_smul,even_price,one_mul,forwards]; simp only [tuner,edges]
    have hh(j:Edge S₀) : ‖Pi.single (M:=fun _:Edge S₀=>G.Color) (x,1) e j‖≤ ‖e‖:=by by_cases hj:(x,1)=j; subst j;simp; simp [Pi.single_apply,Ne.symm hj]
    refine (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add (hh _) (hh _))) ((norm_sub_le ..).trans (add_le_add (hh _) (hh _)))).trans_eq ?_); ring
lemma lamp (x:S₀)(he : 1 < separation B.1 x): curlX s a (tuner e x)=0:=by
    rw [rotated,forwards]; simp_rw [tuner,edges]
    have hh(a':S₀)(d:Axis)(hx:separation B.1 a' ≤ 1): Pi.single (M:=fun _:Edge S₀=>G.Color) (x,1) e (a',d)= 0:=Pi.single_eq_of_ne (by rintro h; exact he.not_ge ((Prod.mk.inj h).1 ▸ hx)) ..
    rw [hh _ _ (Work.E01.sep_step_le ..), hh _ _ (by simp), hh _ _ (Work.E01.sep_step_le ..), hh _ _ (by simp)];simp
lemma still : curlX s a (queue e n (fun _=>1)) = 0:=by
    rw [rotated,forwards]; simp only [tally,sub_self,smul_zero]
noncomputable def chord (p:PlaqAxes)(s:Signed):= p.rotate s -- shadow gauge
noncomputable def pair : PlaqAxes:= ⟨(0,1),by decide⟩
noncomputable def mark (p:PlaqAxes)(e:G.Color) (s:Signed) := if p.rotate s = pair then turned s p • e else 0
lemma markN(p:PlaqAxes)(e:G.Color)(s:Signed): ‖mark p e s‖≤ ‖e‖:=by unfold mark; split; rw [norm_smul, show ‖turned s p‖=1 from (by unfold turned; dsimp only; split_ifs <;>norm_num),one_mul];simp
lemma web (o:S₀)(hu : 10*separation B.1 o < N)(hn:4 ≤ N) : curlX s a (queue e n (fun i=> coord o i 0)) = mark a.2 e s:=by
    rw [rotated,forwards]; let i:= B.2.val.1; let b:= B.2.val.2; let p:= B.1; let g(j:S₀):=coord o j 0; simp only [tally]; rw [coord_step hu hn,coord_step hu hn]; unfold mark
    have hk :i < b:= B.2.property
    change turned s a.2 • ((if b=1 then _ else _) - (if b=1 then _ else _) - ((if i=1 then _ else _) - (if i=1 then _ else _))) = _
    by_cases he: a.2.rotate s=pair
    · have ha: i=0:=congr_arg (fun x:PlaqAxes=>x.val.1) he; have hb:b=1:=congr_arg (fun x:PlaqAxes=>x.val.2) he; rw [if_pos he]; congr 1
      simp [ha,hb,show (Face.send s 0 a).2.val.1=0 from ha,show (Face.send s 0 a).2.val.2=1 from hb, add_smul] --
    have hh:i ≠0∨b≠1 :=by by_contra! h; exact he (Subtype.ext (Prod.ext h.1 h.2))
    rw [if_neg he]; -- cases b / i. `change`
    have hv :b≠1:=by apply (show ∀ i j:Fin 4, i < j → (i≠0∨j≠1) → j ≠ 1 from (by decide)) i b hk hh
    by_cases hx : i=1
    · have he :0≠ (Face.send s 0 a).2.val.2:=by change 0≠b; exact (show ∀ i j:Fin 4,i < j → 0≠j from (by decide)) i b hk
      simp [hv,hx,he]
    simp [hv,hx]
end YM.MSbar.Midpoint

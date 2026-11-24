import YangMills.WilsonProof.NativeSupport.YM.MS.Garment.Apatite
/-!
# Hermitian reality of renormalized prescriptions along real z

Along real $z=0^...$ for Laurent; enough. With real y scaling factor. Keep SP. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool}{m n:ℕ}{U:Rip G}{F H: Mob G}
-- stip

def veil (U:Rip G): Prop:=∀ m i j p,U m i j (-p)=star (U m i j p)
def Sight (F:Mob G): Prop:= ∀ m w, F m (invertMom w)=star ( F m w)
variable (hv:veil U)(hF:Sight F)
lemma InvLift (l:Legs (Shore G m))(h:m≤n): Arts.lift h (invertMom l)= invertMom (Arts.lift h l):= by unfold Arts.lift invertMom; rw [List.map_map,List.map_map]; congr! 1; funext i; exact Prod.ext rfl (map_neg (Left h) i.2)
include hv hF
lemma W_spark (z:ℝ)(p: SectorP m)(l: Legs (Shore G m)): Wtr z U F (-p) (invertMom l)=star (Wtr z U F p l):= by
    -- direct
    have hT(p:SectorP m)(a c: Cfield G m): F m ((a,-p)::(c,- -p)::invertMom l)=star (F m ((a,p)::(c,-p)::l)):= by exact hF m ((a,p)::(c,-p)::l)
    have hp(s t:Bool)(v w): token U F s t v w (-p) (invertMom l)=star (token U F s t v w p l):= by
        unfold token fleck; rw [map_neg,InvLift,hv,star_mul']; exact congr_arg _ (hF (m+1) ((vleg s (hatch (Nat.lt_succ_self m)) v, Left (Nat.le_succ m) p)::(vleg t (hatch (Nat.lt_succ_self m)) w,-Left (Nat.le_succ m) p)::Arts.lift (Nat.le_succ m) l))
    simp only [Wtr,Pi.add_apply,Pi.smul_apply, yeast, at_trc,hv m,hT,hp,star_add,star_sum, smul_eq_mul,star_mul',star_sub, star_natCast, star_ofNat]; simp only [Complex.star_def, Complex.conj_ofReal]
-- core with star integrals
omit hv hF
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {f g:Arc.Tree E ℂ}
lemma dcon (h:ContDiff ℝ ∞ f)(hp:ContDiff ℝ ∞ g)(x:E)(hx:∀ t,f (t,x)=star (g (t,x)))(t:ℝ): Arc.d f (t,x)=star (Arc.d g (t,x)):= by
   have hT:= dr hp x t; obtain hf:= dr h x t; rw [funext hx] at hf; exact hf.unique (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hT)
lemma prune_con (h: ContDiff ℝ ∞ f)(hp:ContDiff ℝ ∞ g)(x:E)(hx: ∀ t,f (t,x)=star (g (t,x)))(n:ℕ)(t:ℝ): pruning n f (t,x)=star (pruning n g (t,x)):= by
   induction n generalizing f g with
   | zero=> exact hx _
   | succ n ih=> change pruning n (chop f) (t,x)=star (_); apply ih (c_chop h) (c_chop hp) (fun t=>?_); unfold chop; simp_rw [dcon (fresh h) (fresh hp) x (dcon h hp x hx)]; rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]; exact integral_conj
lemma cloudStar (z t:ℝ)(h:0<t) : star (cloud z t)=cloud z t := by
    unfold cloud; rw [show 2*(z:ℂ)+1=((2*z+1:ℝ):ℂ) by push_cast; rfl,← Complex.ofReal_cpow h.le]; simp
lemma core_star (f g: Arc.Tree E ℂ)(h:Ultra f)(hp:Ultra g)(x:E)(hx:∀ t,f (t,x)=star (g (t,x)))(z:ℝ)(m:ℕ): coreC (cloud z) m f x=star (coreC (cloud z) m g x) := by
   unfold coreC fetching; simp_rw [Pi.smul_apply,star_smul,star_trivial]; rw [show star (∫ v, fetchP (cloud ↑z) (pruning (m+1) g) v x ∂μhalf) =_ from integral_conj.symm]; congr 1; refine integral_congr_ae ( (ae_restrict_mem measurableSet_Ioi).mono (fun i hi=>?_)); change _=star (cloud (z:ℂ) i*pruning _ _ (i,x)); unfold fetchP; dsimp only; rw [prune_con (h.smooth ()) (hp.smooth ()) x hx,star_mul',cloudStar z i hi]; rfl
include hF hv
lemma featured (h:Form0 b F)(hp:Knot b U)(z:ℝ): Sight (ocean z U F):= by
   intro m l; let s:ℂ:=z; let T(l:Legs (Shore G m)):= Path.wing s U F (ray l); let x:=invertMom l; let f:= carpet (Px m) (T x); let g:=carpet (Px m) (T l)
   have ht(p:SectorP m)(u:ℝ): T x ((-p,u),1)=star (T l ((p,u),1)):= by
       rw [show T x ((-p,u),1)= T x ((-p,-u),1) from (wing_mirror h.token hp.token s (ray x) _ _ _).symm]; simp only [T,Path.wing,ray_sail];
       rw [show x = invertMom l from rfl,InvLift, show slideA (Nat.lt_succ_self m) (-p,-u) = - slideA (Nat.lt_succ_self m) (p,u) from map_neg (slideA _) (p,u), W_spark hv hF z] -- wave rotated
   have hz(v:ℝ): f (v,1)=star (g (v,1)):= by unfold f g carpet Px; rw [← integral_neg_eq_self]; simp_rw [ht]; exact integral_conj
   exact core_star f g (Path.carpet_test h.price hp.price (ray x) s) (Path.carpet_test h.price hp.price (ray l) s) 1 hz z m
end YM.MS.Garment

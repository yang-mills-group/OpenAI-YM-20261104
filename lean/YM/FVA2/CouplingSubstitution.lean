import YM.FVA2.TreeInput

/-!
# `MS.Book.Program.shift` reparametrization of the entire End(quotient)

Finite coupling `q(g*)` calculation as a power series endomorphism.
Define `warp` for the actual entering `Price p` for multi-subset dollar
expansion. The partition in End_Swirl moves by exactly the same clock as the
numerator. Real coupling reexpression, complex tags/towers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clock
open Filter Topology Finset PowerSeries Function
open MS MS.Landau MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Puff.SplitP MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater MS.Native MS.Native.Wilsonian MS.SpaceOut
open Lattice Based Modes Paper Score MS.Swirl.Near
open scoped Topology Classical ContDiff
variable {G:Gauge}{n:Side}
variable {A I E U:Type} {p:Sector A}(e:Cn)
section sub
variable [AddCommGroup E][Module ℂ E]
lemma substitute_unit (V:E): substitute e (useN.refineV V) = useN.refineV V:= by
    funext i; rcases i with _|i; · rw [Program.pay0]
    rw [rules,Finset.sum_eq_single (0:ℕ), Program.cut,pow_zero, coeff_one, if_neg (show i+1≠0 from Nat.succ_ne_zero i), zero_smul]; rotate_left
    · intro k _ he; rw [refineV,if_neg (show k≠useN.origin from he),smul_zero]
    · simp
    rw [refineV, if_neg (show Nat.succ i≠useN.origin from Nat.succ_ne_zero i)]

variable {e}(h:Rooted e)(S: Actors E)
include h
lemma tether : Tether (substitute e) (S.stack useN) (S.stack useN) := ⟨ substitute_unit e S.unit, fun F Z=> Eq.symm (substitute_pair h F Z S.core)⟩
lemma lamp {Q:T E} (hQ:Q 0=0): substitute e (Cheer S useN Q)= Cheer S useN (substitute e Q):= by
   funext i; change substitute _ _ i=(S.stack useN).cheers _ i i; rw [← (tether h S).cheersV, rules,rules]; refine sum_congr rfl fun j hj=> congr_arg (Program.cut e j i • ·) ((overbook S useN Q hQ (show  LE.le j i from Finset.mem_Iic.mp hj)).symm) -- signature test
omit h
section
variable {F:Type}[AddCommGroup F][Module ℂ F]
lemma sensible (M:E→ₗ[ℂ] F)(v:T E) : pointL ℕ M (substitute e v)= substitute e (pointL ℕ M v):= Program.comm e v M
end
end sub
section wick
variable [Fintype A](K:Grain A){e}(h:Rooted e){Q V:SpecB A}{v:T ℂ}
include h
lemma rotate (hx:Endμ K p Q V v)(hq:Q 0=0) : Endμ K p (substitute e Q) (substitute e V) (substitute e v):= by
   have hv: exp0 p (substitute e Q)= substitute e (exp0 p Q) := (lamp h (actor p) hq).symm
   unfold Endμ; rw [hv, ← (tether h (actor p)).craft, (show ∀ v:SpecB A,ℶV K (substitute e v)= _ from fun v=> sensible (View K) v), hx ]; rw [(tether h Toy).craft, (show ∀ v:SpecB A,ℶV K (substitute e v)= _ from fun v=> sensible (View K) v)]
end wick
section series
-- scalar series real.Pinning
variable (t:Team)(x:ℝ)(b:Bool)
def rate : PowerSeries ℝ := PowerSeries.mk fun k=> if k=0 then 0 else if k=1 then 1 else ((t k).coupling.eval x)
lemma bare_shift : shift t x=PowerSeries.map Complex.ofRealHom (rate t x):= PowerSeries.ext fun i=> by rw [shift,coeff_mk,rate,coeff_map,coeff_mk]; split; exact Eq.symm (map_zero _); split; exact Eq.symm (map_one _); rfl
lemma rooted : coeff 0 (rate t x)=0:=by simp [rate]
lemma bare_tangent : coeff 1 (rate t x)=1:=by simp [rate]
def reprℝ (f:PowerSeries ℝ) : PowerSeries ℝ:= PowerSeries.mk fun n=> ∑ i∈Finset.Iic n, coeff n ((rate t x)^i)*coeff i f
lemma compℝ (f: PowerSeries ℝ) : netE (reprℝ t x f)=substitute (shift t x) (netE f):= by
    funext i; rw [netE, reprℝ, coeff_mk,rules,Complex.ofReal_sum]; refine sum_congr rfl fun j _=> ?_; rw [netE,smul_eq_mul,Complex.ofReal_mul,Program.cut, bare_shift,← map_pow, coeff_map]; rfl

lemma pose_shift : posNRG G n (Stripped t) x true= substitute (shift t x) (Score.plainI G n):= by
    let c:= shift t x; let Q:Dot G _root_.YM.Lattice.Cover→ₗ[ℂ] BL (Pos G n) := energyPart G n true
    funext i; cases i with
    | zero=> rw [Program.pay0]; rfl
    | succ i=> unfold posNRG; rw [if_neg (Nat.succ_ne_zero i),style,strip_wobble,rules,rules, map_sum]; refine sum_congr rfl fun j _=>?_ ; unfold Score.plainI; rw [ map_smul ]; split
               next hv=> rw [hv,Program.cut,pow_zero, coeff_one, if_neg (Nat.succ_ne_zero i), zero_smul, zero_smul ]
               rfl
end series

-- scalar extraction, injectivity, monoid map.T sub.
def out : Cn →ₗ[ℂ] T ℂ where
    toFun P i:= coeff i P
    map_smul' _ _:= funext fun _=> PowerSeries.coeff_smul ..
    map_add' _ _:= funext fun _=> map_add ..
lemma out_prod (x y:Cn): out (x*y)= Trunk.core (out x) (out y):= funext fun _=>PowerSeries.coeff_mul ..
lemma out_coeff (x:Cn)(i:ℕ): out x i=coeff i x:= rfl
lemma out_real (x:PowerSeries ℝ) : Score.netE x= out (FormalOPE.RG10.InversionTop.into x):= by ext1 i; rw [ out_coeff, FormalOPE.RG10.InversionTop.into_coeff ]; rfl
-- complex only.Engine coupling commute through ∏ via ring map on Price
variable (p)
local notation "ιP"=>Price p

def prepare (f:Price p) := PowerSeries.mk (substitute e (fun i=>coeff i f))
lemma warp_prepare (f:Price p): track p (prepare p e f)=substitute e (track p f):= by
     funext i; rw [tracking,prepare,coeff_mk]; exact congr_fun (sensible (Dark p).subtype (e:=e) (fun i=>coeff i f)) i

def warp (h:Rooted e): Price p →+* Price p where
   toFun := prepare p e
   map_one':= by apply Paper.rack; rw [warp_prepare, track_one]; exact (tether h (actor p)).unit
   map_mul' a b:= by apply Paper.rack; rw [warp_prepare,Paper.pair,Paper.pair,warp_prepare,warp_prepare]; exact (tether h (actor p)).craft ..
   map_zero':= by apply Paper.rack; rw [warp_prepare,map_zero,map_zero]
   map_add' a b:= by apply Paper.rack; rw [warp_prepare,map_add,map_add,map_add,warp_prepare,warp_prepare]

lemma warp_acts {h:Rooted e} (x:Price p): track p (warp p e h x)= substitute e (track p x):= warp_prepare p e x

def currency : Cn →+* Price p:= PowerSeries.map (algebraMap ℂ (Dark p))
lemma currency_pair (c:Cn)(P:Price p): track p (currency p c * P)= pairW (LinearMap.lsmul ℂ (BL A)) (out c) (track p P):= by
    funext i; rw [pair]; change (∑ j∈antidiagonal i, product p (track p (currency p c) j.1) (track p P j.2))= _; rw [paired]; refine sum_congr rfl fun j _=> ?_ ; rw [tracking (f:=currency p c),currency,coeff_map, cash1,coin_product]; rfl

variable {p}{u:Linear (BL A) ℂ}
omit e in
lemma inLine {V:SpecB A} {Q:Cn}: pointL ℕ u (pairW (LinearMap.lsmul ℂ (BL A)) (out Q) V)= Trunk.core (out Q) (pointL ℕ u V):= by
     funext i; change u (pairW _ _ _ _)=_; rw [paired,map_sum]; exact sum_congr rfl fun i _=> map_smul u _ _
section costend
variable [Fintype A](K:Grain A){Q V:Price p}{u v:T ℂ}
lemma end_scalar (he:Endμ K p (track p Q) (track p V) u)(f:Cn) : Endμ K p (track p Q) (track p (currency p f*V)) (Trunk.core (out f) u):= by
    unfold Endμ; rw [ ← Paper.exp_tracks, ← Paper.pair, mul_left_comm (Paper.exp Q) (currency p f), currency_pair,(inLine (u:=View K)),Paper.pair, Paper.exp_tracks, he ]; exact MS.Puff.Dynamics.mmc (M:=Trunk) ((universe0 _).mpr (fun _=>Submodule.mem_top)) ((universe0 _).mpr (fun _=>Submodule.mem_top)) u -- associative commuting formula arguments
lemma end_sum (S:Finset I)(F:I→Price p)(Z:I→T ℂ)(h:∀ i∈S,Endμ K p (track p Q) (track p (F i)) (Z i)): Endμ K p (track p Q) (track p (∑ i∈S, F i)) (∑ i∈S,Z i):= by unfold Endμ; rw [map_sum,map_sum,map_sum,map_sum]; exact sum_congr rfl (fun i hi=> h i hi)
end costend
end YM.FVA2.Clock

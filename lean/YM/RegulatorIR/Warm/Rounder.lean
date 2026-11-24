import YM.RegulatorIR.Warm.PriceStart
import YM.RegulatorIR.Momentum.Gather

/-!
# Top W1 normalization, no double counting images
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y:Type}{s m p e j r:ℕ}{n:Side}{l P:ℝ}
local notation "L"=> Clocks.flat
variable (H:Even n.val)(hp:l*n.val=P)
lemma tem : Flight (plain L G) (beginF G) (fun _=>0) (fun _=>-1) (Carto G l P H hp) (gliders H):=⟨plain_off _ H hp,always G,fun _=>by decide,fun _ _=>rfl,fun _ _=>rfl,plain_rest L G⟩
lemma stem_zero (p e:ℕ) (he:e≠p): many (beginF G) p e=0:=by
 ext1 i; unfold many massive; simp_rw [fun i=> Warm.placed i G p e he]; simp
local notation "A"=> Carto G l P H hp
variable (ht:Layer.Sym (Carto G l P H hp) (Carto G l P H hp) (finer (moon (X:=G.ColorIndex))))
include ht
omit ht in
lemma pace (x:Horizon G n) :
    let p:=paper G n x; let F:=Flight.foldO (Carto G l P H hp) (beginF G); strum (F 2 2) p= -(costO x):=by
 intro p F; let t:= priceMap (startO L (G:=G) (f:=n));let Z : Meadow G Empty × ℝ × Horizon G n := (0,1,x)
 have hv:= priceStart L H hp x -- args
 have hh: coeff 2 (flavor 2 p F)= -coeff 2 (inscription t Z):=by
    rw [show t=priceMap _ from rfl]
    rw [show inscription t Z= _ from hv, map_sum, ← sum_neg_distrib];
    have hc:=Flight.transit (tem (G:=G) H hp) p (e:=2) (by decide)
    convert hc using 1; apply Eq.symm;apply sum_congr rfl;intro i _;rw [neg_one_mul]; rfl
 rw [inscription,coeff_mk] at hh
 have h:coeff 2 (flavor 2 p F)=drums (F 2) 4 p:=by rw [flavor, PowerSeries.coeff_map,rated_v,speaking];exact language ..
 rw [h, show jet t 2 Z=costO x from ?_] at hh
 swap; exact start_color _ _ -- arg order
 rw [← hh]; unfold drums; rw [sum_eq_single_of_mem 2 (by decide)]; intro i hi he;rw [show F 2 i=0 from ?_,strum_zero]; unfold F Flight.foldO;rw [stem_zero _ _ he]; exact Deck.desk_zero ..
lemma rounds : (Flight.foldO (Carto G l P H hp) (beginF G) 2 2)= (Carto G l P H hp).deckSum (coil (finer (moon (X:=G.ColorIndex)))):=by
 let K:=finer (moon (X:=G.ColorIndex)); let M:= fmat A A K
 rw [show deckSum _ _=coil M from funext (fun i=> deck_costA A K ht i)]
 let T:=Flight.foldO (A) (beginF G)
 apply identified (T 2 2) (coil M) ((tem H hp).printed 2 2) (coil_s M (Quadratic.shines H hp)) (MvPolynomial.funext fun i=>?_)
 rw [← pluck,←pluck]; let y:= (paper G n).symm i
 have hx:(paper G n) y=i:= (paper G n).apply_symm_apply _
 have ht:strum (T 2 2) i= -costO y:=hx ▸ pace H hp y
 rw [ht,← show beneath M y=costO y from congr_fun (Quadratic.sunrise H hp) y];
 have h' := jetInk M (fun _=>y) (k:=0) contDiffAt_const
 rw [show steam M ∘ _=(fun _=> -(beneath M y)) from rfl,tale_base] at h'; apply h'.symm.trans _
 change rhyme (vow (fun _=> paper G n y)) _ 0= _; rw [hx,bold]; rfl
omit ht
-- export spool.F. budget scale invariant.
def tariff_seed (G:Gauge)(j r k:ℕ)(i:Face ℤ) := quota (beginF G i j r) ((path (show 0<(1:ℝ) by norm_num) G.ColorIndex k).diameter)
def handle (G:Gauge)(j r k:ℕ): ℝ≥0∞ := ∑ p:PFace (4:Side),tariff_seed G j r k (reachF p)
lemma handle_fin (G:Gauge) (j r k): handle G j r k≠⊤:=by
 unfold handle; apply ENNReal.sum_ne_top.mpr; intro i _; unfold tariff_seed; apply Oracle.boundedC ((always G _).sized j r); intro x y; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
lemma native_shift (ℓ:ℝ)(x:Long X) : Geometry.seat ℓ x.1=ℓ • Geometry.seat 1 x.1:=by
 let y:=x.1
 have h(x:Cover): Motion.slide ℓ x=ℓ • Motion.slide 1 x:=by ext i; simp
 unfold Geometry.seat glint;rw [smul_add,h,h,smul_comm]
lemma self_tar {a:ℝ}(h:0<a)(G:Gauge)(u:ℕ): path h G.ColorIndex u=path (show 0<(1:ℝ) by norm_num) G.ColorIndex u:=by
 have he : ∀ F B: Tariff (Foot G),F.road=B.road→ F=B:=fun F B h=> by cases F;cases B;congr
 apply he;ext1 x;ext1 y; change Tariff.amount a u (dist (seat a x.1) (seat a y.1))=Tariff.amount 1 u (dist (seat 1 x.1) (seat 1 y.1)); rw [native_shift a x,native_shift a y, dist_smul₀,Real.norm_of_nonneg h.le]; unfold Tariff.amount; field_simp
lemma handled (G:Gauge)(j r k:ℕ)(h:0<l):localQ (path h G.ColorIndex k) (many (beginF G) j r) (handle G j r k):=by
 let he:Even (4:Side).val:=even_two_mul 2
 let P:= Carto G (f:=(4:Side)) (1:ℝ) 4 he (by norm_num);let Q:=gliders he
 rw [self_tar h]; exact Oracle.axi_cost P Q (path (show 0<(1:ℝ) by norm_num) G.ColorIndex k) (fun i=>beginF G i j r) ((tem he (by norm_num)).paves j r) (Oracle.capableM P (u:=k) zero_lt_one)
include ht
lemma launched (h:0<l)(hb:Billed (finer (moon (X:=G.ColorIndex)))) (hv:4≤n.val) : many (beginF G) 2 2=coil (finer (moon (X:=G.ColorIndex))):=by
 let T:= many (beginF G) 2 2; let K:=finer (moon (X:=G.ColorIndex)); let V:=coil K
 ext1 p; let Q(z:Side):=playS (G:=G) (Sight.slab z) H hp; let y(z:Side):=((A).wind (Axial.spark 1 z)) ∘ p
 have hh: Tendsto (fun z=>(Q z).polish (y z)*(Q z).deckSum T ((Q z).project (y z))) atTop (𝓝 (T p)):=by
    apply Axial.melted 1 n H hp hv T ((tem H hp).novel 2 2) p 0
    apply Summable.norm; refine quota_summable (w:=fun x=>(path h G.ColorIndex 0).diameter x.val) (fun x:Hold (X:=Foot G) (0:Fin 2) (p 0)=>Tariff.diameter_unit ..) (ne_top_of_le_ne_top (handle_fin G 2 2 0) (handled G 2 2 0 h (0:Fin 2) (p 0)))
 have hf:= Axial.melted 1 n H hp hv V (coil_r _ K ht) p 0 (coil_f K hb (p 0)) -- hm lemma quota holds exactly x
 apply tendsto_nhds_unique hh
 apply hf.congr;intro z; let e:=Sight.slab z; change (Q z).polish _*(Q z).deckSum _ _=_
 have hr:Layer.Sym (Q z) (Q z) K:=by intro d x y; unfold Q; rw [Halo.steering,Halo.steering]; exact ht ..
 have hq:= rounds (n:=(e*n)) (G:=G) (H.mul_left e.val) (l:=l) (P:=((Sight.slab z).val:ℝ)*P) (by rw [PNat.mul_coe,Nat.cast_mul,mul_left_comm, hp]) hr
 change deckSum (Q z) T= (Q z).deckSum V at hq; rw [hq]
end YM.RegulatorIR.Warm

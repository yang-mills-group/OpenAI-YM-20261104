import YM.OPE.Compatible.Juniper.Turf
/-!
# Growth for padded Δ locations, and accurate reports inside
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
local notation "Fλ"=> fieldX (Shade G)
noncomputable abbrev magnol (G:Gauge)(k:ℕ):= (ozone G 1 1 (heraldD G) zero_le_one (lumenD G) k).choose
def RoadK (b:ℕ):ℝ:=(2*(4*b)+2)+1
lemma ZWealth (a:Fpaper G b): (lawn (ships (moor (pealB a)))+1:ℝ) ≤ RoadK b:=by
       have he: lawn (ships (moor (pealB a)))= (ringO a.1.val).length:= Fin.sum_univ_one _; rw [he]; apply add_le_add_left; have hp:= lengthK a.1.val; have ht:Laurent.size a.1.val.1≤4*b:=bounded a.1.property.1; exact_mod_cast hp.trans (show _≤ 2*(4*b)+2 by omega)
lemma sheetP (y:Fpaper G b)(U:DrawerB G (4*b))(t:ℝ): sheetM (pealB y) (UnB U) t=sheetM (pealB y) (UnB U) t:=rfl -- edit
lemma volt (x y:Fλ)(h:InLine (4*b) x= InLine (4*b) y)(a:Fpaper G b):sheetM (pealB a) x=sheetM (pealB a) y:=by
       funext t; let U:=lotU (t • x); let V:=lotU (t • y); have hv: Agrees ↑(box (4*b)) U V:=by
            intro i hi hj; let j: TilesB (4*b):= ⟨i, hi,hj⟩; change G.lieExp _=G.lieExp _; refine congr_arg _ (congr_fun (show InLine (4*b) (t • x)=InLine (4*b) (t • y) from ?_) j); -- syntax maybe
            rw [map_smul (InLine (G:=G) (4*b)) t,map_smul (InLine (G:=G) (4*b)) t,h]
       let i:=a.1; have he (p:Cover)(hi:p∈Lattice.box b): incG U p=incG V p:= travel_local _ _ _ _ (fun e h h' => hv e (Tumb p hi _ h) (Tumb p hi _ h'))
       have hh:Scav U i.val=Scav V i.val:=by
            unfold Scav Lattice.gauge; have ht:=voles (r:=4*b) (by omega) i; rw [he _ i.property.1,he _ i.property.2, hv _ ht.1 ht.2]
       unfold sheetM board; rw[ringE,ringE]; exact congr_arg (fun u=> G.curvature u a.2) hh
lemma Aurora (x:Fλ)(a:Fpaper G b)(v:ℝ) (j:ℕ): ‖iteratedDeriv j (sheetM (pealB a) x) v‖≤ magnol G j*RoadK b^j*(1+‖InLine (4*b) x‖)^j:=by
       let Q:= InLine (4*b) x; let k:= (1+‖Q‖); have hk:0<k:=add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _); let T:= k⁻¹ • Q; let W:=UnB T; have hh:InLine (4*b) x= InLine (4*b) (k • W):=by rw [map_smul (InLine (G:=G) _), ambry]; exact (smul_inv_smul₀ hk.ne' _).symm
       let u:= pealB a; have hv(i:ℝ): sheetM u (k • W) i= sheetM u W (k*i):=by unfold sheetM; rw [smul_smul i,mul_comm i]
       rw [volt x _ hh a, show sheetM _ _= (fun i=> sheetM u W (k*i)) from funext hv,iteratedDeriv_comp_const_mul ((smoothZ W u).of_le le_top) k]; rw [norm_mul,Real.norm_of_nonneg (pow_nonneg hk.le _),show sheetM u W=_ from funext (moorEq W u)]; let p:= ships (moor u)
       have he(i): ‖indexS i W‖ ≤1:= (chordBudget T i).trans (by unfold T; rw [norm_smul_of_nonneg (inv_pos.mpr hk).le, inv_mul_le_iff₀ hk,mul_one]; exact le_add_of_nonneg_left zero_le_one)
       have hT := (ozone G 1 1 _ zero_le_one (lumenD G) j).choose_spec; apply le_trans (mul_le_mul_of_nonneg_left (hT.2 p W (theater _) (fun i _=>he i) (k*v)) (pow_nonneg hk.le _)); change _ ≤ magnol G j * _ * k^j; rw [mul_comm _ (k^j)]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hk.le _); exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (ZWealth a) _) hT.1
noncomputable def PlateB (j:ℕ) (b:ℕ)(x:Fλ): Scoop G b:= Exposure b (mores x j)
noncomputable def BFilm (b:ℕ)(x:Fλ): JetS (Scoop G b):=⟨PlateB 1 b x,PlateB 2 b x,PlateB 3 b x⟩
lemma BFilm_s (b:ℕ) (x:Fλ): (BFilm b x).s=strideG G b (liftP b x):=by
       ext1 i; rw [show BFilm _ _=⟨_,_,_⟩ from rfl]; change mores x 1 (pealB i)= royal i.1.val x i.2; rw[moreH,champ];rfl
lemma PriceFl (b:ℕ)(j:ℕ)(x:Fλ):‖PlateB j b x‖ ≤ magnol G j*RoadK b ^j *(1+‖InLine (4*b) x‖)^j:=by
       have hh: 0≤ magnol G j:=(ozone G 1 1 _ zero_le_one (lumenD G) j).choose_spec.1; have he:0 ≤RoadK b:=by unfold RoadK; positivity
       refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=>?_ ; change ‖ ((j.factorial:ℝ)⁻¹)* _‖ ≤ _; rw [norm_mul,norm_inv,Real.norm_natCast]; exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr j.factorial_pos))).trans (Aurora x i 0 j)
-- Taylor actual path
lemma borax (b:ℕ)(x:Fλ){t:ℝ}(ht:0<t): ‖Exposure b (t⁻¹ • board (lotU (t • x)))-(BFilm b x).atK t‖ ≤ (magnol G 4*RoadK b^4*(1+‖InLine (4*b) x‖)^4)*t^3:=by
       let D:=magnol G 4*RoadK b^4*(1+‖InLine (4*b) x‖)^4; have hp:0 ≤ D:=by unfold D; have hh:0≤ magnol G 4:=(ozone G 1 1 _ zero_le_one (lumenD G) 4).choose_spec.1; positivity
       apply (pi_norm_le_iff_of_nonneg (mul_nonneg hp (pow_nonneg ht.le _))).2; intro i; let f:=sheetM (pealB i) x; let u:=(BFilm b x).atK t
       have hv:= valueCharge f (smoothZ x _) t ht 3 D hp (fun v=>Aurora x i v 4); have he: ∑ k∈range (3+1), t^k * WardBin.leading k f=t*u i:=by
            rw [sum_range_succ',show WardBin.leading 0 f=0 from by rw [WardBin.leading,iteratedDeriv_zero,show f 0=0 from chargeP ..]; ring]; simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_zero,add_zero]; unfold u JetS.atK; simp only[Pi.smul_apply,Pi.add_apply,BFilm]; change _=t* (WardBin.leading 1 f+t*WardBin.leading 2 f+t^2* WardBin.leading 3 f);ring
       change ‖t⁻¹ * f t- _‖ ≤ D*t^3; rw [show t⁻¹*f t-u i=t⁻¹*(f t-t*u i) by field_simp,norm_mul,Real.norm_of_nonneg (inv_pos.mpr ht).le,inv_mul_le_iff₀ ht]; rw [he] at hv; exact hv.trans_eq (by ring)
end YM.OPE.Spells

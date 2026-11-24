import YM.WilsonCoeffUV.Marked.Paths.Alias
import YM.WilsonCoeffUV.Reclosure.PacketWard
/-!
# Root emission even for field-rank zero (no per-volume convention).
Coordinate ink charges Sprites are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Work.F03
variable {G:Gauge}{n:Side}{k h r t:ℕ}{s A B:ℝ}

-- emission on ANY primitive from path calc Atom; root =0, no translations implicit

def signal (A:Atom G k) (r:ℕ):Ten ℝ (YForest G) r := Blue.fade (plank (lead A) 0) (shine (rye (line A) r)) r
lemma signal_bill (A:Atom G k) (G' : ℕ) (x:Fin G' → YForest G): signal A G' x=∑ i:Fin G' → Grid A, if _h:x=(fun j=> ((i j).1.val,(i j).2)) then rye (line A) G' i else 0:=by
  apply Finset.sum_congr rfl; intro i _; have he j: plank (lead A) 0 (i j)= Pi.single ((i j).1.val,(i j).2) 1:=by rw [plank_origin (lead A) 0 (i j) (j:=((i j).1.val,(i j).2)) rfl]; congr 1; exact Prod.ext (zero_add _) rfl
  simp_rw [he]; split
  next h=> rw [h,shine_lit]; simp
  next h=> obtain ⟨j,hj⟩:= Function.ne_iff.mp h; rw [Finset.prod_eq_zero (Finset.mem_univ j) (Pi.single_eq_of_ne hj _),zero_smul]
lemma signal_seed (A:Atom G k)(n:Side)(x:Fin r→Co n (Hooks G)) : plume (signal A r) n x= rye (meter A (0:Site n)) r x:=by
   let b (i:Grid A):YForest G:= (i.1.1,i.2); let P:=rye (line A) r
   let S i (y: Fin r→YForest G):= if x=foldUnder n ∘ y∧y=b ∘ i then P i else 0
   let v i:= if x=foldUnder n ∘ (b ∘ i) then P i else 0
   have hp y: peglet (signal A r) n x y=∑ i,S i y:=by
      unfold peglet; split
      next h=> rw [signal_bill]; apply Finset.sum_congr rfl; intro i _
               have z: x=foldUnder n ∘ y:=h.symm
               change (if H:y=b ∘ i then P i else 0)=S i y
               by_cases H:y=b ∘ i
               · rw [dif_pos H,show S _ _= P i from if_pos ⟨z,H⟩]
               rw [dif_neg H]; exact Eq.symm (if_neg (fun e=>H e.2))
      next h => symm; exact Finset.sum_eq_zero (fun i _=> if_neg (fun e=>h e.1.symm))
   have hx i: HasSum (S i) (v i):=by
      have he : v i=S i (b ∘ i):=by simp [v,S]
      rw [he]; exact hasSum_single _ (fun j h=> if_neg (fun e=> h e.2))
   unfold plume; simp_rw [hp]; rw [(hasSum_sum fun i (_:i∈ Finset.univ)=>hx i).tsum_eq,Near.frames]; refine Finset.sum_congr rfl fun j _ => ?_
   have hb i: slab A (0:Site n) (j i)=Pi.single (foldUnder n (b (j i))) 1:=by rw [slabrow]; simp; rfl
   simp_rw [hb]; unfold v; split
   next H=> rw [H,shine_lit]; simp [P]
   next H=> obtain ⟨i,hi⟩:= Function.ne_iff.mp H; rw [Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi _),zero_smul]

lemma meter_price (X:Atom G k)(p:Site n)(h:0<s)(r:ℕ): Cork (tor n) p (steep s) (X.budget s*flour G (steep s) k r) (rye (meter X p) r):=by
   let L:= X.magnitude; let v:=steep s; let B:=flour G v k r
   have hl:0≤L:= Finset.sum_nonneg fun _ _=>abs_nonneg _; have hh:0≤B:=flour_nn ..
   have he:0<v:=div_pos h (by norm_num); have hB:0≤ X.budget s*B:= mul_nonneg (mul_nonneg hl (by positivity)) hh
   refine ⟨hB,fun x=>?_⟩
   let u:=tread (tor n) p x
   by_cases hp: rye (meter X p) r x=0; · rw [hp,norm_zero]; exact mul_nonneg hB (by positivity)
   have hv y : (tor n).gap p (stud p x y)≤ X.length:= Fin.cases (show (tor n).gap p p≤_ by rw [(tor n).self _]; omega) (fun i=> belonging X p x hp i) y
   have ht: u≤ X.length+X.length := league_le (tor n) _ (fun i j=> ((tor n).tri _ p _).trans (add_le_add (by rw [(tor n).swap]; exact hv i) (hv j)))
   apply (flourished X p he x).trans
   change L*_ * B ≤ L * _ * B * _
   rw [mul_right_comm L _ B,mul_right_comm L _ B]
   calc
    _ = L*B*Real.exp (v*X.length):= by ring
    _ ≤ L*B* Real.exp (s*X.length+-v*u):= by
      have hx: (u:ℝ) ≤ X.length+(X.length:ℝ):= by exact_mod_cast ht
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity); unfold v steep; nlinarith
    _ = _:=by rw [Real.exp_add]; unfold u v; ring
lemma signal_price (X:Atom G k)(h:0<s)(r:ℕ): Cork Bank.terrain 0 (steep s) (X.budget s*flour G (steep s) k r) (signal X r):=by
    have hz (i:Grid X)(y:YForest G):∀ᶠ (n:Side) in atTop, slab X 0 i (foldUnder n y)=plank (lead X) 0 i y := by simpa only [Near.slab, Bank.casement,map_zero] using pet_index (lead X) 0 i y
    refine ⟨(meter_price X (0:Site 1) h r).1,fun x=>?_⟩
    obtain ⟨n,H,H'⟩:= ((seen (0:Cover) x).and (eventually_all.mpr fun i=>eventually_all.mpr fun j: Fin r=>hz i (x j))).exists
    rw [show signal X r x= rye (meter X (0:Site n)) r (slideC n x) from ?_,← H]; simp only [map_zero]
    exact (meter_price X 0 h r).2 _
    rw [Near.frames]; unfold signal Blue.fade; apply Finset.sum_congr rfl; intro i _; congr 1; exact Finset.prod_congr rfl fun j _=> (H' (i j) j).symm
lemma meter_origin (A:Atom G k)(p:Site n)(v:Link G n): Tendsto (fun b:ℝ=> (b^k)⁻¹ • meter A p (b • v)) cutRay (𝓝 (Tensor.diagonal (inkNote p A) v)):=by
   unfold Tensor.diagonal; rw [ink_note]; simpa only [meter,input, map_smul, Atom.poly,div_eq_inv_mul, smul_eq_mul] using atom_limit A p (arm G n 1 v)
lemma meter_shell (A:Atom G k)(p:Site n) :Rays k (meter A p):= ray_origin fun v=> ⟨_,meter_origin A p v⟩
lemma meter_lift (A:Atom G k)(p:Site n) : Tensor.coeff (meter A p) k 0= Tensor.symmetrize (inkNote p A):=by
    have he:= (meter_hot A p).contDiffAt (x:=0); apply Tensor.ext_diag _ _ (Tensor.coeff_symm (he.of_le le_top)) (Tensor.symmetrize_sym _); funext v; rw [Tensor.symmetrize_diagonal]; exact tendsto_nhds_unique (ray_limit he.analyticAt (meter_shell A p) v) (meter_origin A p v)
private lemma hold (A:Atom G k)(h:A.Invariant)(x:Site n)(U:Config G n)(t):A.unmasked (Lattice.gauge t U) x=A.unmasked U x:=by simp only [Atom.unmasked,Work.F05.slot_gauge]; exact h _ _
lemma meter_ward (A:Atom G k)(h:A.Invariant)(n:Side) : let P:=sprig (meter A (0:Site n)) k; rollTest (flash P) (flash P) 1 0:=by
    intro P Z _ q U W p; let F:=meter A (0:Site n)
    have he x:Green (meter A x):= (meter_hot A (x:Site n)).contDiffAt
    have hx i (hi:i<k): rye F i=0:= funext fun u=>by
       have hp:iteratedFDeriv ℝ i F 0=0:= (rays_jet ((he 0).analyticAt) k).mp (meter_shell A (0:Site n)) i hi
       rw [rye,hp]; simp
    have ht: PowerSeries.X^k*flash P=jet F:= moves F (fun i hi=> by rw [jet_apply,hx _ hi,map_zero])
    have hf :∀ᶠ z in 𝓝 (0:Lawn Z), F (U z)=F (W z):=by
       filter_upwards [p.shift] with w h'; unfold F meter; simp_rw [Mosaic.mantle_input]; rw [h', Lattice.pull_id]; exact hold _ h _ _ _ |>.symm
    apply mul_left_cancel₀ (a:=(PowerSeries.X:Blue.Ink Z)^k) (pow_ne_zero _ X_ne_zero)
    conv_lhs=>arg 1; arg 1; rw [← train_X (Blue.spool U)]
    conv_rhs=>arg 1; arg 1; rw [← train_X (Blue.spool W)]
    rw [← map_pow,←map_pow,←map_mul,←map_mul,ht, traveling _ p.g₀ p.f₀ _ (he 0),traveling _ p.g₁ p.f₁ _ (he 0)]; exact jet_congr hf
end YM.WilsonCoeffUV.Mer.Rolls

import YM.OPE.Compatible.Grid.Read
import YM.OPE.Compatible.Grid.List
/-!
# Anchored gauge-completions of a scripted marker. General all shell polynomials including Null†.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Page Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s b U D:ℝ}{d r m k q:ℕ}
-- deterministic minimal route
abbrev carryP (x: Cover): Walk:= route 0 x 1
def ringO (p:Edge Cover): Walk:= carryP p.1 ++ [posDir p.2] ++ Lattice.reverse (carryP (p.1+step p.2))
lemma volley (p:Edge Cover): stop (0:Cover) (ringO p)=0:=by
     unfold ringO carryP; rw [stop_append,stop_append,route_end]; erw [show stop p.1 [posDir p.2]=p.1+step p.2 from rfl, show stop (p.1+step p.2) _=0 from by have ht:=reverse_stop (route 0 (p.1+step p.2) 1) (0:Cover); rw [route_end] at ht; exact ht] -- rec
lemma lengthK (p:Edge Cover): (ringO p).length ≤ 2 * size p.1+ 2 := by
     unfold ringO Lattice.reverse carryP; simp only [List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_reverse]; simp_rw [Stationary.route_length,sub_zero]; have ht := Laurent.size_add p.1 (step p.2); have hs:size (step p.2:Cover)=1:=by simp [size,Lattice.step,Pi.single_apply,apply_ite (fun i:ℤ=>i.natAbs)]
     omega
abbrev shipP (x:Cover×Shade G): Beam G:= ⟨ringO (x.1,x.2.1),(pleatsF x.2.2).toContinuousLinearMap⟩
abbrev ships (p:Page (Shade G) r): Chant G r:= fun i=> shipP (p i)
lemma supportM (p:Page (Shade G) r): (lawn (ships p))+1 ≤ (2*r+3)*stamp p:=by
     rw [perimeter]; have he: lawn (ships p)≤ ∑ i,(2*Laurent.size (p i).1+2):=sum_le_sum fun i _=> lengthK _; rw [sum_add_distrib,← mul_sum,sum_const, card_univ,Fintype.card_fin,nsmul_eq_mul] at he; let T:=∑ i,Laurent.size (p i).1; change _≤ (2*r+3)*(1+T); change lawn _≤2*T+r*2 at he; nlinarith
lemma theater (p:Page (Shade G) r): moderateX (ships p) (heraldD G):= fun _ _=> ((pleatFit G).choose_spec.2 _ _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
-- ON RAW link test (ACTUAL)
abbrev testQ (p:Script (Shade G) r): CoverConfig G→ℝ:= rhythm ships p
def board (V:CoverConfig G): fieldX (Shade G):= fun k=> G.curvature (travel V 0 (ringO (k.1,k.2.1))) k.2.2
lemma issue (p:Page (Shade G) r)(U:CoverConfig G): wordX (fun _=>board U) p= verseX (ships p) U:= prod_congr rfl fun _ _=> (pleatsEq _ _).symm
lemma boardGauge (v:Cover→ G.El)(U:CoverConfig G): board (Lattice.gauge v U)= plumeX (v 0) (board U):=by ext1 i; unfold board; rw [travel_gauge, volley, Gauge.curvature_conjugate]; rfl
lemma boardPrice (U: CoverConfig G): Quiet (board U) 0:=by
      obtain ⟨D,hD⟩:= (isCompact_univ : IsCompact (Set.univ:Set G.El)).exists_bound_of_continuousOn G.continuous_curvature.continuousOn; refine ⟨D,(norm_nonneg _).trans (hD 1 (Set.mem_univ _)),fun i=>?_⟩; rw [show poise 0 _=(1:ℝ) by unfold poise; rw [pow_zero],mul_one]; unfold board; exact (PiLp.norm_apply_le _ _).trans (hD _ (Set.mem_univ _))
lemma signalV (p: Script (Shade G) r)(h:p.painted)(hP: soot m p b) (U:CoverConfig G)(x:Cover→G.El): testQ p (Lattice.gauge x U)= testQ p U:=by
       have he(u): testQ p u=wholeX p (fun _=>board u):=tsum_congr (fun i=> congr_arg (p i*·) (issue _ _).symm)
       simp_rw [he,boardGauge]; exact script_color hP h _ (d:=fun _=>0) (fun _=> boardPrice _) (by simp)
-- ζ a₂, budgets first
lemma paySpray (G:Gauge)(m q k r:ℕ)(hq:m+2*r≤q):∃ Z:ℝ,0≤Z∧∀ (p:Script (Shade G) k)(b:ℝ), soot q p b→ soot m (timbre ships p r) (Z*b)∧Sack (fun i:Page (Shade G) k×Page (Shade G) r=>figure m i.2) (uncurry (fun j i=>p j*coff (ships j) r i)) (Z*b) :=by
    obtain ⟨C,hc,H⟩:=coffP G k r _ m (lumenD G); let f:ℕ:=2*k+3; let Z:= C*(f:ℝ)^(m+2*r); have hz:0 ≤ Z:=by unfold Z; positivity
    refine ⟨Z,hz,fun p b h=>?_⟩
    have ht(i:Page (Shade G) k): soot m (p i • coff (ships i) r) (Z*(figure q i*‖p i‖)):=by
        apply (Sack.scale_line (H _ (theater i)) _).tips; let l:=m+2*r; have he: (lawn (ships i)+(1:ℝ))^l≤ (f:ℝ)^l*figure q i :=by
             apply le_trans (pow_le_pow_left₀ (show (0:ℝ) ≤ _ from by positivity) (show (lawn (ships i)+(1:ℝ))≤ (f:ℝ)*↑(stamp i) from (show _ from by exact_mod_cast supportM i)) _); rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast notch_one i.xy) hq) (by positivity)
        exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hc) (norm_nonneg (p i))).trans_eq (by change ‖p i‖*(C*(_*_))=_; unfold Z; dsimp [l]; ring)
    have hg : SumBudget (fun i=>Z*(figure q i*‖p i‖)) (Z*b):=⟨fun i=>mul_nonneg hz (h.1 i),h.2.1.mul_left _,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hz⟩; exact ⟨Sack.draws ht hg (payer m),Sack.barrel ht hg⟩
lemma doReads {p:Script (Shade G) k}(h: soot q p b)(hq:2*r≤ q)(v:Fin r→fieldX (Shade G))(hn:Glob v (fun _=>0)): HasSum (fun i=>p i*wholeX (coff (ships i) r) v) (wholeX (timbre ships p r) v):=by
       let S:= fun (j:Page _ k) i=> p j*coff (ships j) r i*wordX v i; choose b hb H using hn; have hg:= (paySpray G 0 q k r (by omega)).choose_spec.2 _ _ h |>.2
       have hS: Summable (uncurry S):=by
          apply (hg.2.1.mul_left (∏ i,b i)).of_norm_bounded; rintro ⟨j,i⟩; unfold S; simp only [uncurry_apply_pair]; rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (wordXbill hb H (show (∑ j:Fin r, (0:ℕ)) ≤ 0 by simp) i) (norm_nonneg _)).trans_eq (by ring)
       have hx j: (∑' i,S j i)= p j * wholeX (coff (ships j) r) v :=by unfold S wholeX; simp only [_root_.mul_assoc,tsum_mul_left]
       have ht : Summable fun i=>∑' j,S i j:= hS.prod; simp_rw [← hx]; unfold wholeX timbre; rw [show (∑' i:Page _ _, (∑' j,p j*coff (ships j) r i)*wordX v i)=(∑' i,∑' j, S j i) from tsum_congr fun i=>by unfold S; rw [tsum_mul_right],hS.tsum_comm]; exact ht.hasSum
end YM.OPE.Flume.Script

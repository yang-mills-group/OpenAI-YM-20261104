import YM.SignedWilsonExpansion.F9.Usher
/-! # Assembly at grade, including actual raised position noise. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type}{Y μ ν θ g:ι→ℝ}{L:Filter ι}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→ PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable {S:SectionData (F.level d)} (hS:S.Sound P')(p0: Bid.pop S)(v₀:d≤h)
variable (Bf:FrontQ q L Y g μ ν)
variable (Pp:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))
local notation "ξ"=>billSize
variable (α:(F.level d).Index)(i:(F.level h).Index)
lemma pays_mark (v:Maxer L Y): Wage L Y 1 (remitW q 1):=Wage.enroll (IsBigO.of_norm_le fun i=> by rw [remitW,pow_one,Real.norm_of_nonneg ((q i).mark_pos.le)]; exact (q i).small)
variable {Z:ι→(F.level d).Coeff} (t': SizeW L μ (F.level d) Z){E': (F.level d).Coeff}
include t' p0 Pp hS v₀ Bf
lemma account_full (j:ℕ)(hj:j≤e): Salary L μ (fun i=> (q i).billSize d) ℂ (fun i=>account Wn (q i) S (Z i) j):=by
    simp_rw [accounting]; apply Salary.many Bf.inside_; intro i _; simpa only [mul_one] using Salary.tilt (Wage.mul (owed (Y:=μ) (L:=L) q d) (t'.paid i)) (Salary.shift (sober_paid q Wn Bf.pol _ hS p0 v₀ i Pp hj) Bf.ahead)
lemma heady (h:wt Rι i=d)(j:ℕ)(hj:j≤e): Wage L μ 1 (fun j'=> sonar Rι i (account Wn (q j') S (Z j') j)):=by
    simp_rw [show ∀ j',sonar Rι i (account Wn (q j') S (Z j') j)=_ from (fun a=> assembleParts i _ h)]
    apply Wage.fix (((account_bill q Wn hS p0 v₀ Bf Pp t' j d v₀ hj).pass (Normalize.en v₀)) (sonar Rι i)) (.refl ..); exact Eventually.of_forall fun i=> inv_mul_cancel₀ (pow_ne_zero _ (q i).mark_pos.ne')
-- `thermalV` head h, no full Budget.H angular assumption beyond Γ event.Convergence at every antenna (grid and neighbors)
def θprobe (α:(F.level d).Index)(Z:(F.level d).Coeff)(x:PorchK W' F Q' Ω R h k u): ℂ:= (x.duty d*Z α)* sonar Rι i (x.sober Wn S α 0)
def νprobe (v₀:d≤h)(i:(F.level h).Index)(E':(F.level d).Coeff)(α:(F.level d).Index): ℂ:= E' α* sonar Rι i (vista F (upL F v₀ α))
variable (hc:Crest L Y ν θ (F.level d) Z r E')
include hc
omit p0 Pp hS v₀ t' in
private lemma crest_tends (hp:r ≤ wr (F.level d) α) : Tendsto (fun j=> Z j α) L (𝓝 (E' α)):=by
    have he:= Wage.next_zero (hc.campus α hp) Bf.slope; have ht:Tendsto (fun i=>(θ i:ℂ)* E' α) L (𝓝 (((1:ℝ):ℂ)*E' α)):= (Complex.continuous_ofReal.continuousAt.tendsto.comp hc.head).mul tendsto_const_nhds; simpa only [Complex.ofReal_one, one_mul,zero_add] using ((he.add ht).congr (fun i=> sub_add_cancel _ _))
lemma earns_scan (w:wt Rι i=d)(hx:r≤wr Rι i): Tendsto (fun j=> θprobe (S:=S) Wn i α (Z j) (q j)) L (𝓝 (νprobe v₀ i E' α)):=by
   unfold θprobe νprobe; by_cases V: E' α=0
   · rw [V,zero_mul]; by_cases v:r≤wr (F.level d) α
     · have hb:= earSolo q Wn hS p0 v₀ Bf Pp α i 0 d (Nat.zero_le _) w; have hu:= hc.campus α v; rw [V] at hu; simp only [mul_zero,sub_zero] at hu; refine Wage.next_zero (Wage.fix ( Wage.mul (Wage.mul (owed (Y:=Y) (L:=L) q d) hu) hb ) ( .refl .. ) (?_)) Bf.slope; refine Eventually.of_forall fun j=>?_ ; change ((_)⁻¹* _)*remitW q d j=_; rw [mul_right_comm, inv_mul_cancel₀ ?_,one_mul]; exact pow_ne_zero _ (q j).mark_pos.ne'
     have hv:= Wage.transfer (lamp_small q Wn Bf.pol Bf.stretch Pp S hS p0 v₀ α i w (Nat.lt_of_lt_of_le (not_le.mp v) hx)) Bf.ahead; apply Wage.next_zero (Wage.fix (( Wage.mul ( Wage.mul (owed (Y:=μ) (L:=L) q d) (t'.paid α)) hv )) (.refl ..) (?_)) Bf.mass; refine Eventually.of_forall fun i=>?_ ; change ((_)⁻¹* 1)*remitW q (d+1) i= _; unfold remitW; rw [mul_one,pow_succ,← mul_assoc, inv_mul_cancel₀ ?_,one_mul]; exact pow_ne_zero _ (q i).mark_pos.ne'
   have ht:= hc.pure α V; let u:= sonar Rι i; refine Tendsto.congr (fun i=> by rw [mul_assoc,mul_left_comm]) (Tendsto.mul (crest_tends (q:=q) Bf α hc (show _ from ?_)) (solo_equal q Wn hS p0 v₀ Bf Pp α i w ?_ ?_)) -- congr orientation & param
   · exact (congr_arg Prod.snd ht).symm.le
   · exact congr_arg Prod.fst ht
   exact (congr_arg Prod.snd ht).trans_le hx
lemma launch_tend (w:wt Rι i=d)(hx:r≤wr Rι i):
    Tendsto (fun j=> sonar Rι i (account Wn (q j) S (Z j) 0)) L (𝓝 (sonar Rι i (Normalize.up v₀ (bulb G d ((F.level d).coords.symm E'))))):=by
   let Z':= (F.level d).coords.symm E'; let u(j α):= θprobe (S:=S) Wn i α (Z j) (q j); let Y:= sonar Rι i; simp_rw [accounting,map_sum,map_smul]; have he: Y (Normalize.up v₀ (bulb G d Z'))= ∑ j:(F.level d).Index,νprobe v₀ i E' j:=by nth_rw 1 [← (F.level d).basis.sum_repr Z']; simp only [map_sum,map_smul]; apply Finset.sum_congr rfl; intro j _; unfold νprobe; rw [pressUp, carried, show ((F.level d).basis.repr Z') j= E' j from congr_fun ((F.level d).coords.apply_symm_apply E') j]; rfl -- replace
   rw [he]; exact tendsto_finsetSum Finset.univ fun i' _=> earns_scan q Wn hS p0 v₀ Bf Pp i' i t' hc w hx
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa

import YM.OPE.Compatible.Streams.Iota
/-! # H beam through stand within register -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier
variable {u d s r l k m:ℕ}{W I:Type}{τ:Phase→ℕ}
variable {n c:Side}(x y:Site n)(H:Even n.val)(v:ℝ){T:Plot H}(i:T.Free)
include H in
lemma SettleQ (h:Settle x y v): Settle y x v:=by
      intro k; have ht:= tourD x (decks k y) k; rw [← decks_plus H, twinned,Weir.flats,separation_comm x] at ht; rw [← show separation (decks k x) y = _ from ht]; exact h _
lemma placedDist (e:RootEdge): separation x (placed n x e).1 ≤ size e.1:=by
     unfold placed; rw [separation_comm]; unfold separation; simp only [add_sub_cancel_left]; exact within_size ..
lemma phrase (e:edgeV n)(h:pathX H e=i.val)(b:edgeV n)(he:pathX H b=i.val): ∃ k:Kv,b=ferry k e:=by
      let k:= (edgesK H).tick b; let j:= (edgesK H).tick e; have hx: ferry k i.val.val=b:=by rw [← he]; exact (resettle H b).symm
      have hy: ferry j i.val.val=e:=by rw [← h]; exact (resettle H e).symm
      exact ⟨k+j,by rw[←hy,←ferry_plus H,add_assoc,twinned,add_zero,hx]⟩
lemma BeamF (e:RootEdge)(hs: pathX H (placed n x e)=i.val)(h:Settle x y v)(he:0 ≤ v): BeamNear H T i y (v*(1+size e.1)):=by
      intro j hp; obtain ⟨z,rfl⟩:= phrase H i _ hs _ hp; apply (h z).trans
      rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ he; let a:=placed n x e; have ht:separation (decks z x) y ≤ size e.1+1+separation y (ferry z a).1:=by
            have he':= ferry_gap z a; have hu:= tourD x a.1 z; have hy:= separation_triangle (decks z x) (decks z a.1) (ferry z a).1; have hQ:= separation_triangle (decks z x) (ferry z a).1 y; rw [separation_comm y]; have hx:= placedDist x e; change separation x a.1 ≤ size e.1 at hx; omega
      have he':0 ≤ ((size e.1):ℝ):=Nat.cast_nonneg _; apply ((Nat.cast_le (α:=ℝ)).mpr ht).trans; push_cast; unfold a; nlinarith
-- wind estimated to WTax irrespective of r<d
lemma quitZ (y:Keys G T.Free)(e:edgeV n): ‖offZ H T y (whiz e)‖≤ ‖y‖:=by
      rw [hub_r]; unfold hover; split <;> rename_i d
      all_goals rw [show T.rollX y _= T.cite 0 y _ from rfl]; unfold Stand.cite; split<;> first|simp|exact norm_le_pi_norm ..
      exact norm_le_pi_norm ..
variable [Fintype I](K:I→RootEdge)(F: Libra.Keys G I→G.Color)
noncomputable abbrev Scent (e:RootEdge):=2*(2+size e.1+∑ i:I,size (K i).1)
lemma actsHere (e:RootEdge)(o:Kv)(he:Plate H T i o= placed n x e) (hp': Scent K e ≤ n.val): AwayZ H T i o (F∘ dip K n x):= by
       intro k hk p q hp; apply congr_arg F; ext1 j; change p (sett n x (K j))=q _; apply hp; intro h; have hu:Plate H T i o≠ Plate H T i k := fun he=>hk.symm ((edgesK H).together he)
       have hx:= Vast H _ _ (show pathX H (Plate H T i o) = pathX H (Plate H T i k) from by unfold Plate;rw [path_ferry,path_ferry]) hu|>.2; rw [h,he] at hx; have hv:= single_le_sum (f:=fun i:I=>size (K i).1) (fun i _=>Nat.zero_le _) (mem_univ j)
       have hV:= separation_triangle (placed n x e).1 x (placed n x (K j)).1;rw [separation_comm (placed n x e).1 x] at hV; unfold Scent at hp'; have hQ:= placedDist x e; have hy:= placedDist x (K j); omega
variable (n':W→ Side)(H':∀ i,Even (n' i).val)(T':∀ i,Plot (H' i))(x':(i:W)→Site (n' i))
lemma scentPaid (u:G.ColorIndex) (hv:ContDiffAt ℝ ω F 0) (he:r ≤ d): WindT n' 0 (d+2) 1 fun i=>Pawn.mold (WindV (H' i) (T' i) (F∘ dip K (n' i) (x' i)) u) r:=by
     intro j; let A(i):= dip K (n' i) (x' i) ∘L offZ (G:=G) (H' i) (T' i); let p:= ((Phone G).coord u) ∘ F; let q:= Tensor.coeff p (r+j.val) 0; let Z(i):= WindV (H' i) (T' i) (F∘ dip K (n' i) (x' i)) u; have ht(w:Libra.Keys G I): (Pawn.mold p r w).seq j.val=q (fun _=>w):=by fin_cases j<;>rfl
     have hz:= ((Phone G).coord u).toContinuousLinearMap.contDiff.contDiffAt.comp 0 hv; refine ⟨⟨‖q‖,norm_nonneg _,fun i y=>?_⟩,fun i=> tallJ _ _ _⟩; change ‖(Pawn.mold (Z i) r y).seq _‖ ≤ _; rw [show Pawn.mold (Z i) r= Pawn.mold p r ∘ A i from moldC (A i) p hz r]; rw[ Function.comp_apply,ht]; apply (q.le_opNorm _).trans; rw [prod_const,card_univ,Fintype.card_fin]; have hV : ‖A i y‖ ≤ 1+‖y‖:= (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun j=>(quitZ _ _ _).trans (le_add_of_nonneg_left zero_le_one)); unfold care; rw [pow_zero,Pi.one_apply,one_mul,one_mul]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hV _).trans (pow_le_pow_right₀ (by simp) (by have hh:j.val<3:=j.isLt; omega))) (by positivity)
end YM.OPE.Variance

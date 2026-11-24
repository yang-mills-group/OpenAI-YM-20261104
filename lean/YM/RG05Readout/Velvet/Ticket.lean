import YM.RG05Readout.Velvet.Reprise
import YM.RG05Readout.Aligned.Limits
/-! Orientation and rank: kernel bulk writes exact *same* packet's evaluations on authorized collars. Reader.Gram price occurs externally. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Harvest Halls
open RG MergeProof Flatten PhysicalNext.Repeat Legato Dash Extraction.Lease Petals Push.RelayDifference
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{v m n o j d:ℕ}{q R η a ζ:ℝ}
local notation "δ"=> C.S.a
variable (D:Poem C j) {s:Fin v→ℕ}{Ψ:Wave (Fin v)} (h:Sky Ψ R η)
open Chalice Poem
variable (he:0<q)(hp:R*q<C.S.a j/2)
local notation "H"=> telegram D h he hp
local notation "I"=> Fin v
local notation "V"=> Points v
local notation "L"=> tsupport D.opening.val
local notation "E"=> Points (v+D.n)
local notation "S!"=> E4 × Points D.n
open OPE Orbits Spec
variable {S:YM.Table C.book}{f:Extraction.Order}(U:Spec.Final C f S)(W:Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (p:Viewers U) (x:(i:Fin v)→ C.label (s i))
local notation "F"=> fleet s x D
local notation "w₀"=> fun i:Fin D.n=> (D.token i).1
local notation "v'"=> fun i:Fin v=> S.project (s i) (x i)
local notation "w'"=> fun i:Fin D.n=> S.project (D.token i).fst (D.token i).snd
local notation "Z"=> spectator U p
local notation "g"=> D.opening.val
local notation "p!"=> pluck D
variable (ha: ∀ z∈ scoreHull Ψ,∀ k≤d, orbitMargin W.port k (WithLp.ofLp (beginAt q 0 z)) 0)
def packing (W:Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(q:ℝ)(Ψ:Wave (Fin v))(d:ℕ)(V':Orbits.Labels S s)(u:Points v):= pattern Ψ u • W.packet d (WithLp.ofLp (beginAt q 0 u)) V' 0
local notation "C0"=> packing U W q Ψ d
noncomputable def coeff (W:Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(d:ℕ)(V':Orbits.Labels S s)(q:ℝ)(Ψ:Wave (Fin v)):S.Field d:= ∫ u:V, packing U W q Ψ d V' u
local notation "Y"=> coeff U W d v' q Ψ
local notation "w!"=> fun i:Fin D.n=>D.token i
local notation "b"=>cardReading D Z x q Ψ
include ha h
lemma packed (V':Orbits.Labels S s) : Integrable (packing U W q Ψ d V'):=by
    let s₁(u:Points v):=WithLp.ofLp (beginAt q 0 u); let p(u:Points v):= W.packet d (s₁ u) V' 0; have hx:Continuous s₁:=(bag v).continuous.comp (begin_cont.comp (continuous_const.prodMk continuous_id))
    have he': Continuous (pattern Ψ):=(Pulse.lit Ψ 0|>.continuous).comp (bag v).continuous
    have hu: Continuous (C0 V'):=by
       apply mul_joint (pattern Ψ) p he'; intro u hv; change ContinuousAt (fun u:Points v=>∑ i:Fin (d+1), U.sector.derivatives.rise (d:=i.val) _ (W.fresh i.val (s₁ u) 0 V')) u
       unfold ContinuousAt; apply tendsto_finsetSum; intro i _; let g':= U.sector.derivatives.rise (d:=i.val) (e:=d) (Nat.le_of_lt_succ i.isLt); exact ((LinearMap.toContinuousLinearMap g').continuous.continuousAt.comp ((W.fresh_smooth i.val (s₁ u) 0 V' (ha u (patterned_sub hv) _ (Nat.le_of_lt_succ i.isLt))).continuousAt.comp (f:=fun z=> (s₁ z,0)) ((hx.prodMk continuous_const).continuousAt)))
    apply hu.integrable_of_hasCompactSupport; have h:HasCompactSupport (pattern Ψ):= pattern_support h.park; exact h.smul_right
omit ha h
lemma loving (u:V) (t:E4): W.packet d (WithLp.ofLp (beginAt q t u)) v' t=W.packet d (WithLp.ofLp (beginAt q 0 u)) v' 0:=by
   let a:=beginAt q 0 u; unfold Orbits.Reader.packet; refine Finset.sum_congr rfl (fun i _=> congr_arg (U.sector.derivatives.rise (d:=i.val) (Nat.le_of_lt_succ i.isLt)) ?_)
   have he:=W.fresh_transport i.val a.ofLp 0 (d:=s) v' t; rw [zero_add,show (fun j=> a j+t)= (beginAt q t u).ofLp from (funext fun j=>by change a j+t=t+q • u j; unfold a; rw [short,zero_add,add_comm])] at he; exact he
lemma head_links {t:S!}(hp:t.2∈ rim D)(he:t.1∈ L): Injective (beside (sole t.1) (WithLp.ofLp t.2)):=by
    have hA:0<C.S.a j/2:=half_pos (C.S.a_pos _); obtain ⟨hf,hv⟩:= sentries D he hp; refine beside_distinct.mpr ⟨injective_of_subsingleton _,fun i k hi=>?_,fun _ i hx=>?_⟩
    · by_contra he; specialize hv _ _ he; rw [hi,sub_self,norm_zero] at hv; linarith only [hv,hA]
    specialize hf i; rw [show t.1=t.2 i from hx,sub_self,norm_zero] at hf; linarith only [hf,hA]
include U
lemma headLine {t:E4× Points D.n}(hv:t.1∈ L)(hy:t.2∈ rim D)(u:C.label d): S.read (Points.cons t.1 t.2) (Fin.cons (⟨d,u⟩:C.book.Token) D.token)=upon S d t.1 (WithLp.ofLp t.2) w' (S.project d u):= by -- unselected here
   let x:=t.1; let y:=WithLp.ofLp t.2; have he:= head_links D hy hv; let v:=D.token
   have hx:= head_observe (n:=D.n) (e:=Equiv.refl _) S v ⟨d,u⟩ U.room.kernel.laws.toSymmetric he; exact hx.symm.trans (Aligned.whole_classes U (sole (⟨d,u⟩:C.book.Token)) v _ _ he none)
-- returns ANY observer extension using S.respects
lemma camera {t:V}{y:Points D.n}(hf:ribbon t y ∈ conf (v+D.n)):
   (spectator U p).read (ribbon t y) F= whole Z t.ofLp v' y.ofLp w':=by
    let e:I⊕ Fin D.n≃ Fin (v+D.n):=finSumFinEquiv
    let a:=fun j:I=>(⟨s j,x j⟩:C.book.Token)
    let z:=t.ofLp; let u:=y.ofLp; let r:=(ribbon t y).ofLp
    have hq: r ∘ e=beside z u:=funext (fun i=>by rcases i with i|i; exact Fin.append_left ..; exact Fin.append_right ..)
    have hw:F ∘ e= beside a D.token:= funext (fun i=>by rcases i with i|i; exact Fin.append_left a D.token i; exact Fin.append_right a D.token i)
    have hv:Injective r:= hf
    have hx: observe Z (beside z u) (beside a D.token)=observe Z r F:=by rw [←hq,←hw]; exact perm_observe Z (spectate U p).laws.toSymmetric e F hv
    exact (named_fin Z (spectate U p).laws.toSymmetric F hf).symm.trans (hx.symm.trans (Aligned.whole_classes U a _ _ _ (hq ▸ (hv.comp e.injective)) p))
end YM.RG05Readout.Velvet

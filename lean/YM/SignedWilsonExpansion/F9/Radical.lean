import YM.SignedWilsonExpansion.F9.Insignia
/-!
# Inversion price of Commission ground on actual Label–Observable lift
Eff using rank move in HS filtration. This nil is exact before `Layout`, not an assertion of
means per visible tuple.
-/
set_option autoImplicit false
set_option maxHeartbeats 275000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec Formal)
open Tape
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
variable (q': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
section ranks
def Bide (F:Labels.Frame G h)(z:ℕ): Submodule ℂ (Label G h) where
    carrier:={x|∀ i:F.Index,z≤ wr F i→ F.coords x i=0}
    zero_mem':=fun _ _=>by rw [map_zero]; rfl
    add_mem':= fun {x y} p q i u=> by rw [map_add,Pi.add_apply,p i u,q i u, add_zero]
    smul_mem':= fun c {x} p i u=> by rw [map_smul,Pi.smul_apply,p i u, smul_zero]
lemma val_rankH (F:Labels.Frame G h)(x:Label G h)(p:x∈ Grade (i,j))(u:j<d): x∈Bide F d:=by
    intro y v; apply F.power_coefficient _ _ p; intro H; have hz:j=wr F y:=congr_arg Prod.snd H; omega
abbrev BideW (F:Labels.Frame G h)(z:ℕ): Submodule ℂ (Sec G h):= (Bide F z).comap (XSpace.On.sectionMap h)
lemma bider (F:Labels.Frame G h) (r:ℕ) : ∀ x∈ Bide F r,bulb G h x∈ BideW F r:=by
    intro x h'; rw [← F.basis.sum_repr x,map_sum]; apply Submodule.sum_mem; intro i _; rw [map_smul]; by_cases p:wr F i<r
    · exact Submodule.smul_mem _ _ (val_rankH F _ (projector_grade (F.pure i)) p)
    rw [show F.basis.repr x i=0 from h' i (not_lt.mp p), zero_smul]; exact Submodule.zero_mem _
lemma vista_rank (i:(F.level h).Index) (p:wr Rι i<r) : vista F i∈ BideW Rι r:=by rw [carried]; exact bider _ _ _ (val_rankH _ _ ((F.level h).pure i) p)
lemma moverank (F:Labels.Frame G h)(p:d≤l): BideW F d ≤ BideW F l:= fun _ x i h=> x i (p.trans h)
variable (t':Mesh)(ρ:ℝ)(ht:t'.spacing=sizeT A ρ c)
lemma Mora_above (v:d≤h)(i j:(F.level d).Index)(w:wt (F.level d) i=d)(p:wr (F.level d) i≤wr (F.level d) j): coeff 0 (q'.Mora v i j)=if j=i then 1 else 0:=by
    let F':= F.level d; let a:=wr F' i; unfold Stair.Mora; rw [stampsFee _ _ _ (Nat.zero_le _)]
    rcases lt_or_eq_of_le p with p|p
    · rw [if_neg (show j ≠ i from fun x=>Nat.lt_irrefl _ (x ▸ p))]; exact (loft_upper (q'.supply d v) (q'.charm d v) i p).2 (⟨j,rfl⟩:TagIx F' (wr F' j))
    let I':TagIx F' a:=⟨i,rfl⟩; let J':TagIx F' a:=⟨j,p.symm⟩; change paper (q'.raft v I'.val) 0 (Nat.zero_le _) J'= _; rw [tie (q'.supply d v) (q'.charm d v) I' w]; by_cases h:j=i
    · rw [if_pos h,show J'= I' from Subtype.ext h,Pi.single_eq_same]
    rw [if_neg h,Pi.single_eq_of_ne (fun q=>h (Subtype.ext_iff.mp q))]
include ht
lemma flag_above (v:d≤h)(i j:(F.level d).Index)(w:wt (F.level d) i=d)(p:wr (F.level d) i≤wr (F.level d) j): coeff 0 (q'.flagTape W t' ρ v i j)=if j=i then 1 else 0:=by
   unfold flagTape; rw [inked,map_smul,q'.Mora_above W v i j w p]; by_cases x:j=i; · subst x; rw [if_pos rfl,w, ←ht, mul_inv_cancel₀ (pow_ne_zero _ t'.positive.ne'),one_smul,Complex.ofReal_one,if_pos rfl]
   simp [x]
lemma radical_down (i:(F.level h).Index): (q'.originalT W t' ρ 0-bulb G h) ((F.level h).basis i)∈ BideW Rι (wr Rι i):=by
   rw [LinearMap.sub_apply,published0,hingeK,printTape,Finset.sum_apply,← carried]; let Q:= F.level h; let d:=wt Rι i; let k:=wr Q i; let u:=Q.bound i; let i':=downL F u i (le_refl d); let p(j):= flagTape W q' t' ρ u i' j; let y(j:(F.level d).Index):= Normalize.up u (vista F j); have hi:wt (F.level d) i'=d:= congr_arg Prod.fst (down_grade F u i (le_refl d)); have hy:wr (F.level d) i'=k:=congr_arg Prod.snd (down_grade F u i (le_refl d)); let V(j):= coeff 0 (p j) • y j
   have hx: upL F u i'=i:=up_down ..; have hE: V i'=vista F i:=by unfold V; rw [flag_above W q' t' ρ ht u i' i' hi le_rfl]; rw [if_pos rfl,one_smul]; exact (pressUp ..).symm.trans (congr_arg (vista F (h:=h)) hx)
   change (∑ j:(F.level d).Index,V j)-_ ∈ _; rw [← hE,← Finset.add_sum_erase _ V (Finset.mem_univ i'),add_sub_cancel_left]; apply Submodule.sum_mem; intro j h'; by_cases w: wr (F.level d) j< k; · unfold V y; rw [← pressUp]; exact Submodule.smul_mem _ _ (vista_rank _ (lt_of_le_of_lt (congr_arg Prod.snd (up_grade F u j)).le w))
   unfold V p; rw [ flag_above W q' t' ρ ht u i' j hi (hy.trans_le (le_of_not_gt w)),if_neg (Finset.mem_erase.mp h').1, zero_smul]; exact Submodule.zero_mem _
lemma radical_out (x:Label G h)(p:x∈Bide Rι (r+1)):
    (q'.originalT W t' ρ 0-bulb G h) x∈ BideW Rι r:=by
   rw [← (F.level h).basis.sum_repr x,map_sum]; apply Submodule.sum_mem; intro i _; rw [map_smul]; by_cases z:wr Rι i≤ r
   · exact Submodule.smul_mem _ _ (moverank _ z (q'.radical_down W t' ρ ht i))
   rw [show (F.level h).basis.repr x i=0 from p i (by omega),zero_smul]; exact Submodule.zero_mem _
/-! reference tangent section into permitted signed basis, preserves filtrations. -/
abbrev ladderS (h:ℕ): Sec G h→ₗ[ℂ] Label G h:= XSpace.On.sectionMap h
omit ht in
def upsTurn (M: Label G h→ₗ[ℂ] Sec G h): Module.End ℂ (Sec G h):= (1-(M ∘ₗ (ladderS h)))
lemma radicalNil : (upsTurn (q'.originalT W t' ρ 0))^(h+1) =0:=by
    let M:= q'.originalT W t' ρ 0; let V:= upsTurn M; have hv(r x)(p:x∈ BideW Rι (r+1)): V x∈BideW Rι r:=by
       have hE: V x= -((M-bulb G h) (ladderS h x)):=by change x-M (ladderS h x) = -(_-_); rw [show bulb G h (ladderS h x)=x from bulb_recovers ..]; abel
       rw [hE]; exact Submodule.neg_mem _ (q'.radical_out W t' ρ ht _ p)
    have he(n x)(p:x∈BideW Rι n): (V^n) x=0:=by
       induction n generalizing x with
       | zero=> apply Eq.trans (show (V^0) x=x from by rw [pow_zero,Module.End.one_apply]); have ht:ladderS h x=0:= ((F.level h).coords).injective (funext (fun i=> (p i (Nat.zero_le _)).trans (congr_fun (map_zero (F.level h|>.coords)) i).symm)); rw [← bulb_recovers G h x, show XSpace.On.sectionMap h x=0 from ht, map_zero]
       | succ n ih=> rw [pow_succ,Module.End.mul_apply]; exact ih (V x) (hv n x p)
    apply LinearMap.ext; intro x; exact he (h+1) x (fun i h'=> by have ht:wr Rι i≤ h:= value_le _ i; omega)
end ranks
end Stair
end YM.WilsonCoeffUV.Mer.Xa

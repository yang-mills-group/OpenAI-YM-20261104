import YM.MS.Motif.Channel
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Vary
/-!
# Separate oriented antibracket action for classical Landau seed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment
open scoped Topology ContDiff
variable {A:Type}{G:Gauge}{n:ℕ} {F H:Rack G n}
abbrev channelSide (a:Cfield G n): Bool:= a.1.2
def split0' (G:Gauge)(n:ℕ):Cfield G n ≃ (Bool×Chan G n) where
    toFun i:=(channelSide i, mote i)
    invFun i:=onX i.1 i.2
    left_inv _:=rfl
    right_inv _:=rfl
lemma pairedX (p:Chan G n)(b:Bool): channelSide ( onX b p )=b:= rfl -- redundant c
lemma phase_par (p:Chan G n): parity (onX true p)= !(parity (onX false p)):= by rcases p with ⟨_|p,r⟩ <;> rfl
lemma phase2 (p:Chan G n): phase p*phase p=1:=by unfold phase; split <;> norm_num
lemma at_plain (a b:Chan G n)(u v:Bool)(x:SectorP n) : (2:ℂ)* Wick.D0 G n (onX u a) (onX v b) x=(if a=b ∧ u≠v then phase a else 0):= by
   rcases a with ⟨_|a,y⟩ <;> rcases b with ⟨_|b,x'⟩ <;> cases u <;> cases v <;>
     simp [Wick.D0,Landau.choir,onX,phase,laplace,mul_ite,Landau.delta] <;> first|(by_cases h:a=b <;> by_cases ht:y=x' <;> norm_num [h,ht]) | (by_cases h:y=x' <;> norm_num [h])
-- spawn and the other orientation. Always odd. require F even.
local notation "S" => field ( Landau.parity (A:=Arts.L n) (C:=G.ColorIndex)) -- careful F shadows

def glow0 (u:Bool)(F:Rack G n)(p:Chan G n): Rack G n:= fun l=>phase p* F ((onX (!u) p,-net l)::l)
def shoots (u:Bool) (F:Rack G n) : Op ( Shore G n ) ℂ:= ∑ i:Chan G n, quash Landau.parity ( onX u i ) ( glow0 u F i )
lemma pull_ahead (b:Bool)(p:Chan G n)(hf:Pure S false F): Pure S (true ^^ parity (onX b p)) ( glow0 b F p ):= by
    intro l hl; unfold glow0; apply mul_eq_zero_of_right; apply hf; rw [degree_cons]; have hz: parity (onX (!b) p)=(true ^^ parity (onX b p)):= (by rcases p with ⟨_|p,j⟩ <;> cases b <;> rfl); change (parity (onX (!b) p) ^^ degree S l) ≠ false; have hL : degree S l ≠ parity (onX (!b) p) := hz ▸ hl; exact neqB hL
where neqB {a b:Bool}(h:a≠b): (b ^^ a)≠false:= by cases b <;> cases a <;> first| decide| contradiction

lemma blastD (p q:Chan G n)(u v:Bool)(l r:Legs (Shore G n)) (hf:Pure S false F) : radius Landau.parity (Wick.D0 G n) (onX u p) (onX v q) F H l r=if p=q ∧ u≠v then glow0 v F p l* H ((onX v p,net l)::r) else 0:= by
   unfold radius; dsimp only; rw [at_plain]; split <;> rename_i hx; swap; · simp only [zero_mul]
   obtain ⟨rfl, hV⟩:= hx; unfold glow0; simp_rw [neg_neg]; let p':=p -- maybe p subst
   have h':u=!v:= by cases u <;> cases v <;> simp_all
   by_cases he:degree S l=parity (onX u p)
   · rw [he]; have ht:cross (parity (onX v p)) (parity (onX u p))=(1:ℂ):= by cases v <;> cases u <;> rcases p with ⟨_|p,j⟩ <;> first|rfl|contradiction
     rw [ht,one_mul,← h']
   rw [← h']; rw [hf _ (by rw [degree_cons]; exact (by change (parity (onX u p) ^^ degree S l) ≠ false; cases hc:degree S l <;> cases hq:parity (onX u p) <;> simp only [hc,hq] at * <;> first|decide| contradiction))]; ring
lemma hearth (h:Pure S false F): tree parity (Wick.D0 G n) F H= (shoots false F) H+(shoots true F) H:= by
    funext l; let P:= allocate S l (R:=ℂ); unfold tree; rw [shoots,shoots]; simp only [Pi.add_apply,LinearMap.sum_apply,Finset.sum_apply]; simp_rw [quamped,tip]; rw [← sp0,← sp0]; change P _=P _+P _; rw [← map_add]; apply scatter_congr; intro u v hp; rw [convertR ( Wick.reverse_d G n)]; have ht (f:Cfield G n→ℂ): ∑ i,f i = ∑ i:Bool, ∑ j:Chan G n,f (onX i j):= by rw [← Equiv.sum_comp (split0' G n).symm f,Fintype.sum_prod_type]; rfl
    rw [ht]; simp_rw [ht (fun i:Cfield G n=> radius Landau.parity _ _ i _ _ _ _)]; simp_rw [ blastD _ _ _ _ u v h]; simp
end YM.MS.Motif

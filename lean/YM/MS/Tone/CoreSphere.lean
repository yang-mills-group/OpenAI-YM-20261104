import YM.MS.Tone.Ropes
/-! Derive actual Q from S₂ without tune assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}
local notation "B"=>Branch G Axis
abbrev s₀ (G:Gauge):=run (Wilsonian.core G 0)

def α₂ (p:QP)(a b:Atom Axis):ℂ:= match a,b with
 | (some a,false),(some b,false)=> - (precision a b (wave p):ℂ)
 | _,_=>0
def styleK (p:QP)(i j:B):ℂ:= matchA i.2 j.2 (α₂ p i.1 j.1 + μ2 p i.1 j.1)
lemma art_two (a b:Atom Axis)(p:QP)(i j: G.ColorIndex): run (weightW G idRail (0:Cover)) [((a,i),p),((b,j),-p)] = matchA i j (α₂ p a b) := by
    rcases a with ⟨_|a,_|_⟩ <;> rcases b with ⟨_|b,_|_⟩ <;> first | exact normW p a b i j| dsimp only [α₂]
    all_goals simp only [matchA,ite_self]; refine w_off _ _ ?_; solve| left; intro i; simp [Landau.gauge] | right; intro i; simp [Landau.gauge]
lemma rankTwo (p:QP)(i j:B): s₀ G [(i,p),(j,-p)]=styleK p i j:= by
   unfold s₀; rw [Wilsonian.at_rest,Book.levels, Tone.grade, Book.enough _ (by simp)]
   rcases i with ⟨a,i⟩; rcases j with ⟨b,j⟩; simp only [Wilsonian.W, bosons,map_add,Pi.add_apply,mantra,art_two,styleK]; unfold matchA; split <;> simp
lemma core_rank : Book.rank 2 (s₀ G):= by unfold s₀; rw [Wilsonian.at_rest,Book.levels,Tone.grade]; exact Book.rankMod _ 2

variable (F: Score G Axis QP)
open Flux
lemma put_in (r: List (LightMode G QP))(i:B)(p:QP) : attaches parity (Kzone G) (s₀ G) F [(i,p)] r= ∑ j:B, (send wave).table i j p* F ((j,p)::r):= by
    rw [bolt_F]; simp only [knob,net_cons,degree_cons,degree_nil,Bool.xor_false, show net (A:=B) ([]:List (Mode B QP))=0 from rfl,add_zero];
    have hv a:s₀ G [(a,-p),(i,p)]=styleK (-p) a i:= by simpa only [neg_neg p] using rankTwo (-p) a i
    rcases i with ⟨⟨_|i,_|_⟩,x⟩ <;> simp only [hv,Fintype.sum_sum_type,Fintype.sum_prod_type];
    all_goals
      simp [Spectrum, leggin, signA,styleK,μ2,α₂,matchA,Bonded.fee,Landau.p,field,parity,Fintype.sum_option, send,bare,Landau.choir, ite_mul,mul_ite, wave_neg, cross]
end YM.MS.Tone.Frame

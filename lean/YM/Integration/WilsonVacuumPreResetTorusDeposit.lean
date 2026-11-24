import YM.Integration.WilsonVacuumPreResetTorusActionRead
import YM.AllOrder.Floe.Pit

/-! The corrected finite Wilson series determines a dated layout of its own
original path atoms. At equal grade and rank the entries are interlaced, which
adds their actual tariffs and preserves both rank-two displacement moments. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusDeposit
open Gauge Wilson RG Lattice
open AllOrder AllOrder.Floe AllOrder.Floe.StateE
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Extra.Iteration
open scoped Classical BigOperators
variable {G:Gauge}

def address (a:PrismA G):Age:=
  ⟨a.grade-3,a.rise,by have bound:=a.rankA; omega⟩

theorem coordinates (a:PrismA G)(h:3≤a.grade):
    (address a).e=a.grade ∧ (address a).r=a.rise+2:=by
  constructor
  · change a.grade-3+3=a.grade
    omega
  · rfl

def bank : SeriesA G → Layout G
  | [] => fun i _=>Extra.Iteration.blank G i.r
  | a::tail => fun i=>if row:address a=i then
      Extra.Iteration.join (row ▸ a.cells) (bank tail i)
    else bank tail i

def fee (C:ℝ):SeriesA G → Age → ℝ
  | [],_=>0
  | a::tail,i=>if address a=i then C+fee C tail i else fee C tail i

private theorem component {s grade:ℕ}{P:Stack G s}{σ C:ℝ}
    (enrolled:Commission P σ C grade)(older:0<grade):Quoted P σ C:=by
  refine ⟨enrolled.toll,enrolled.hue,?_⟩
  intro h
  have eqn:s=0:=by omega
  subst s
  exact enrolled.loan older

private theorem joined {k:ℕ}{P Q:ℕ→Atom G k}{σ A B:ℝ}
    (hp:Quoted P σ A)(hq:Quoted Q σ B):
    Quoted (Extra.Iteration.join P Q) σ (A+B):=by
  refine ⟨join_cost hp.pay hq.pay,join_sym hp.symm hq.symm,?_⟩
  intro q
  subst k
  exact join_silent (hp.mute rfl) (hq.mute rfl)

theorem quoted (Z:SeriesA G){σ C:ℝ}(issued:∀a∈Z,Commission a.cells σ C a.grade)
    (late:∀a∈Z,0<a.grade)(i:Age):Quoted (bank Z i) σ (fee C Z i):=by
  induction Z with
  | nil =>
    refine ⟨blank_cost σ,fun _=>blank_sym,?_⟩
    intro q
    have all (k:ℕ)(h:k=2):Silent (ι:=ℕ) (h ▸ fun _=>Extra.Iteration.blank G k):=by
      subst k
      exact blank_silent
    exact all i.r q
  | cons a T ih =>
    have q:=ih (fun x hx=>issued x (List.mem_cons_of_mem _ hx))
      (fun x hx=>late x (List.mem_cons_of_mem _ hx))
    by_cases row:address a=i
    · subst i
      have h:=component (issued a (List.mem_cons_self ..)) (late a (List.mem_cons_self ..))
      simpa [bank,fee,address] using joined h q
    · simpa only [bank,fee,dif_neg row,if_neg row] using q

theorem total {C:ℝ}(pos:0≤C)(Z:SeriesA G)(i:Age):
    fee C Z i≤(Z.length:ℝ)*C:=by
  induction Z with
  | nil => simp [fee]
  | cons a T ih =>
    simp only [fee,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    split <;> linarith

theorem legal (Z:SeriesA G){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (late:∀a∈Z,3≤a.grade)(T:Finset Age):Legal T (bank Z):=by
  have h (i:Age):=quoted Z draw.2 (fun a member=>lt_of_lt_of_le (by decide :0<3) (late a member)) i
  exact ⟨fun i _=>⟨σ,fee C Z i,width,(h i).pay⟩, fun i _=>(h i).symm⟩

end YM.Integration.WilsonVacuumPreResetTorusDeposit

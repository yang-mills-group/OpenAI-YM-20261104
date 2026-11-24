import YM.MSbar.Bristol.Money
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {A w B C b r a d v Y e:ℝ}{T W:List σ}{p i j m k s:ℕ}{g: Positions σ→ℝ}{L:σ→ Site c} (u:σ)
variable (ha: 0 < a)(h:Multiplicity L k)(hv:a*(m+2)+b≤ r)(hb:0 ≤ b)
variable (ht:∀ i:ℕ, (1+(i:ℝ))^p ≤ Y* Real.exp (a*i)) (hx:0≤C)(hh:0≤d)
-- merge near & remote.Upload.Hour
variable {Q: Set (Positions σ)}{f: Positions σ→List σ→ℝ}{W_: List σ→ℝ}
variable (hs:∀ x:Positions σ,x∈Q →∀ L':List σ,L'.length=m+1 → |buoy g x L'|≤ C* raiseQ L r L')
variable (hM:∀ x:Positions σ,x∈Q→ ∀ l:List σ, l.length=m+1 → peaks L l ≤ j →|buoy g x l-f x l|≤ d)
variable (he:∀ l:List σ,l.length=m+1→0 ≤ W_ l∧∀ x∈Q, |f x l|≤ W_ l) (hi:∀ i:σ,Yarn m (fun l:List σ=>W_ (i::l)*swipe L b p (i::l))≤ A)
include h ha hb hv hh ht hx hs hM
lemma patch (hY:0 ≤ Y)(hk:0<w) (h₁:0≤A)(e':∀ l:List σ,l.length=m+1→0 ≤ W_ l∧∀ x∈Q,|f x l|≤W_ l)(hh':∀ i:σ,Yarn m (fun l:List σ=>W_ (i::l)*swipe L b p (i::l)) ≤ A):
      JetTab L b p w Q g m (w^(m+1)*(checkU C Y d b a k p m j+A)):=by
     let G₁:= shorn j L r C d; let K(i:List σ):=G₁ i+ W_ i; have hG(i):0≤ G₁ i:=by unfold G₁ shorn; split;exact hh; exact mul_nonneg hx (Real.exp_pos _|>.le)
     let d':= checkU C Y d b a k p m j; have hD:0≤d':=by unfold d' checkU; have hx:=wpos b p j; have hy:=count_pos ha;positivity
     let v:= w^(m+1); have hV:0<v:=pow_pos hk _; refine ⟨mul_nonneg hV.le (add_nonneg hD h₁),fun i=>K i *v,fun i hl=>⟨mul_nonneg (add_nonneg (hG _) (e' _ hl|>.1)) hV.le,fun x he' =>?_⟩,fun i=>?_⟩
     · apply mul_le_mul_of_nonneg_right _ hV.le; unfold K G₁ shorn;split
       next he => have hx:= abs_add_le (buoy g x i - f x i) (f x i); rw [sub_add_cancel] at hx; exact hx.trans (add_le_add (hM x he' i hl he) (e' _ hl|>.2 _ he'))
       next he=> exact (hs x he' i hl).trans (le_add_of_nonneg_right (e' _ hl|>.1))
     refine le_trans (le_of_eq (b:=v*Yarn m (fun l:List σ=> K (i::l)*swipe L b p (i::l))) ?_) (mul_le_mul_of_nonneg_left ?_ hV.le); · rw [←sheen]; refine stitch _ fun l _=>?_ ; ring
     unfold K; simp_rw [add_mul,pockets]; exact add_le_add (churn i ha h hv hb ht hx hh hY) (hh' i)
lemma cache (hY:0 ≤ Y)(hk:0 < w) (hQ:Q={0})(hp:0≤v)(he:∃ f':Positions σ→ℝ, JetTab L b p w {0} f' m v ∧ Lodge.summit L b p (fun T=> f 0 T-buoy f' 0 T) m A) (hA:0≤ A):
      JetTab L b p w Q g m (w^(m+1)*(checkU C Y d b a k p m j+(A+v/w^(m+1)))):=by
     subst Q; obtain ⟨f',hf,hA'⟩:= he; let W'(L':List σ):=|f 0 L'|; refine Bristol.patch ha h hv hb ht hx hh hs hM hY hk (add_nonneg hA (div_nonneg hp (pow_pos hk _|>.le))) (W_:=W') (fun L hl=>⟨abs_nonneg _,fun x he=>by rw [Set.mem_singleton_iff.mp he]⟩) (fun i=> ?_); refine le_trans ?_ (add_le_add (hA' i) (JetTab.count hf hk 0 (Set.mem_singleton _) i)); rw [←pockets]; refine shiny _ fun l hl=>?_ ; let L':=i::l; let R':= swipe L b p L'; rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ (effect ..|>.le); exact (show |f 0 L'|= |f 0 L'-buoy f' 0 L'+buoy f' 0 L'| from congr_arg abs (sub_add_cancel ..|>.symm)).le.trans (abs_add_le ..)
end YM.MSbar.Bristol

open import Data.Nat
open import Data.Fin
open import Data.List using (List ; map)
open import Data.Vec using ([]; _∷_)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (refl)

import etfj
import itfj renaming (Ctx to ICtx)

module diagram (n : ℕ) where

-- Object is represented by 0
module FJ = etfj 0
-- We have 'n' classes
module IFJ = itfj n

open FJ 
open IFJ 

-- Elaborating types

postulate 
  Ty⇒Name : Ty → Name
  Name⇒Ty : Name → Ty

-- Elaborating context

elabCtx : Ctx → ICtx
elabCtx Γ = map (λ v → Name⇒Ty (proj₂ v)) Γ

-- Elaborating class table

open FJ.ClassTable
open IFJ.ClassTable

elabMSig : Meth → MSig
elabMSig m = record { ret = Name⇒Ty (Meth.ret m) ; params = map (λ p → Name⇒Ty (proj₂ p)) (Meth.params m) }

elabFlds : List (Name × Name) → List Ty
elabFlds flds = map (λ f → Name⇒Ty (proj₂ f)) flds

elabCSig : Class → CSig
elabCSig c = record { flds = elabFlds (Class.flds c) ; signs = map (λ m → elabMSig (proj₂ m)) (Class.meths c) }

postulate
  elabCT : CT → CTSig

-- Elaborating expression

postulate
  Δ : CT

open FJ.Syntax
open FJ.Typing Δ
open IFJ.Syntax (elabCT Δ) renaming (Expr to IExpr)

elabVar : ∀ {Γ x c} → Γ ∋ x ∶ c → Name⇒Ty c ∈ elabCtx Γ
elabVar here = here refl
elabVar (there wtv) = there (elabVar wtv)

elabField : ∀ {f c} → (flds : List (Name × Name)) → flds ∋ f ∶ c → Name⇒Ty c ∈ elabFlds flds

elabExpr : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → IExpr (elabCtx Γ) (Name⇒Ty τ)
elabExpr (T-Var x) = Var (elabVar x)
elabExpr (T-Field {flds = flds} wte wtf f) = Field (elabExpr wte) {!elabField flds f!}
elabExpr (T-Invk wte x x₁) = Invk (elabExpr wte) {!!} {!!}
elabExpr (T-New {C = C} flds wtcp) = New (Name⇒Ty C) {!!}

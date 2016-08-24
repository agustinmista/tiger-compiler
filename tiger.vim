" Vim syntax file
" Language: Tiger!!
" Maintainer : Martín Ceresa
" Latest Revision: 11 August 2015
"
" Based on pig.vim. http://www.vim.org/scripts/script.php?script_id=2186

if exists("b:current_syntax")
    finish
endif

" Keywords
syn keyword tigerLanguageKeywords type array of var function let in end if then else while do for to break nil

" Operators
" syn keyword tigOpers '&' '|' '<' '>' '<=' '>=' 

" Types
syn keyword tigType int string

" Runtime Functions
syn match tigFunction "\<[a-zA-Z][a-zA-Z0-9_]*\s*(" contains=tigRuntime
syn keyword tigRuntime print flush getchar ord chr size substring concat not exit contained

" Literals
syn match tigNumber "[0-9]*"
syn region tigString		start=+"+  skip=+\\\\\|\\"+  end=+"+

" Region
syn region tigComment start="/\*" end="\*/"

" Todo.
syn keyword tigTodo TODO FIXME XXX DEBUG NOTE contained

let b:current_syntax = "tiger"

hi def link tigComment  Comment
hi def link tigerLanguageKeywords Statement
hi def link tigRuntime Function
hi def link tigNumber Number
hi def link tigTodo Todo
hi def link tigString String
hi def link tigType Type


create table results (
   run        text    not null,
   lang       text    not null,
   backend    text    not null,
   benchmark  text    not null,
   trial      integer not null,
   t_compile  real,
   t_run      real,
   ans        text,
   err        text,
   primary key (run, lang, backend, benchmark, trial),
   foreign key (run) references runs (run)
);

create table runs (
  run            text  not null primary key,
  run_timestamp  text,  -- YYYY-MM-DD HH:MM:SS
  hostname       text
);

create table commits (
  commit_hash       text  primary key,  -- 14 characters
  commit_timestamp  text,               -- YYYY-MM-DD HH:MM:SS
  commit_msg        text
);

create table ci_runs (
  commit_hash       text  primary key,
  run               text
);

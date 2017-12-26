[RFC 4253 transport] : (comp, non first_kex_packet_follows)

client-conn-init < conn-done  < client-id < kex-begin < cli-kex-init < kex <
                   (server-*)   server-id               ser-kex-init

cli-kexdh-init < ser-kexdh-reply < cli-newkeys < kex-done
                                   ser-newkeys

[learned OpenSSH]
(cli)     (ser)     (cli)   (ser)   (ser)     cli
KEXINIT < KEXINIT < KEX30 < KEX31 < NEWKEYS < NEWKEYS
SR_*                ^       ^
UNIMPL              SSH_MSG_KEXDH_INIT, SSH_MSG_KEXDH_REPLY
DEBUG
IGNORE
KEX30

[ssh -v -v -v]
...
debug1: Connecting to den.rexy.xyz port 7777.
debug1: Connection established.
...
debug1: Local version string SSH-2.0-OpenSSH_7.6
debug1: Remote protocol version 2.0, remote software version OpenSSH_7.2p2 Ubuntu-4ubuntu2.2
debug1: match: OpenSSH_7.2p2 Ubuntu-4ubuntu2.2 pat OpenSSH* compat 0x04000000
...
debug1: SSH2_MSG_KEXINIT sent
debug1: SSH2_MSG_KEXINIT received
...
debug2: local client KEXINIT proposal
...
debug2: peer server KEXINIT proposal
...
debug2: first_kex_follows 0
...
debug1: kex: algorithm: curve25519-sha256@libssh.org
debug1: kex: host key algorithm: ecdsa-sha2-nistp256
...
debug3: send packet: type 30
debug1: expecting SSH2_MSG_KEX_ECDH_REPLY
debug3: receive packet: type 31
...
debug1: Host '[den.rexy.xyz]:7777' is known and matches the ECDSA host key.
debug1: Found key in /Users/Rex/.ssh/known_hosts:2
debug3: send packet: type 21
...
debug1: rekey after 134217728 blocks
debug1: SSH2_MSG_NEWKEYS sent
debug1: expecting SSH2_MSG_NEWKEYS
debug3: receive packet: type 21
debug1: SSH2_MSG_NEWKEYS received
...
debug1: rekey after 134217728 blocks
...

[relevant excerpt from RFC 4253]
The client initiates the connection.

The server MAY send other lines of data before sending the version string.
The primary use of this feature is to allow TCP- wrappers to display an error message before disconnecting.

When the connection has been established, both sides MUST send an identification string.

Key exchange will begin immediately after sending this identifier.

In the compatibility mode, the server SHOULD NOT send any further data after sending its identification string until it has received an identification string from the client.
In the compatibility mode, the server MUST NOT send additional data before the identification string.

When compatibility with old clients is not needed, the server MAY send its initial key exchange data immediately after the identification string.

Key exchange (kex) begins by each side sending name-lists of supported algorithms.

Each side MAY guess which algorithm the other side is using, and MAY send an initial key exchange packet according to the algorithm, if appropriate for the preferred method.

the guess is considered to be right, and the optimistically sent packet MUST be handled as the first key exchange packet.

However, if the guess was wrong, and a packet was optimistically sent by one or both parties, such packets MUST be ignored (even if the error in the guess would not affect the contents of the initial packet(s)), and the appropriate side MUST send the correct initial packet.

A key exchange method uses explicit server authentication if the key exchange messages include a signature or other proof of the server’s authenticity. A key exchange method uses implicit server authentication if, in order to prove its authenticity, the server also has to prove that it knows the shared secret, K, by sending a message and a corresponding MAC that the client can verify.

The key exchange method defined by this document uses explicit server authentication. However, key exchange methods with implicit server authentication MAY be used with this protocol. After a key exchange with implicit server authentication, the client MUST wait for a response to its service request message before sending any further data.

Key exchange begins by each side sending the following packet:byte	SSH_MSG_KEXINIT

first_kex_packet_follows
Indicates whether a guessed key exchange packet follows. If a guessed packet will be sent, this MUST be TRUE. If no guessed packet will be sent, this MUST be FALSE.

After receiving the SSH_MSG_KEXINIT packet from the other side, each party will know whether their guess was right. If the other party’s guess was wrong, and this field was TRUE, the next packet MUST be silently ignored, and both sides MUST then act as determined by the negotiated key exchange method. If the guess was right, key exchange MUST continue using the guessed packet.

After the SSH_MSG_KEXINIT message exchange, the key exchange algorithm is run. It may involve several packet exchanges, as specified by the key exchange method.
Once a party has sent a SSH_MSG_KEXINIT message for key exchange or re-exchange, until it has sent a SSH_MSG_NEWKEYS message (Section 7.3), it MUST NOT send any messages other than:
Transport layer generic messages (1 to 19) (but SSH_MSG_SERVICE_REQUEST and SSH_MSG_SERVICE_ACCEPT MUST NOT be sent);
Algorithm negotiation messages (20 to 29) (but further SSH_MSG_KEXINIT messages MUST NOT be sent);
Specific key exchange method messages (30 to 49).

Note, however, that during a key re-exchange, after sending a SSH_MSG_KEXINIT message, each party MUST be prepared to process an arbitrary number of messages that may be in-flight before receiving a SSH_MSG_KEXINIT message from the other party.

Key exchange ends by each side sending an SSH_MSG_NEWKEYS message. This message is sent with the old keys and algorithms. All messages sent after this message MUST use the new keys and algorithms.

When this message is received, the new keys and algorithms MUST be used for receiving.

The purpose of this message is to ensure that a party is able to respond with an SSH_MSG_DISCONNECT message that the other party can understand if something goes wrong with the key exchange.

This is implemented with the following messages. The hash algorithm for computing the exchange hash is defined by the method name, and is called HASH. The public key algorithm for signing is negotiated with the SSH_MSG_KEXINIT messages.
First, the client sends the following:
byte	SSH_MSG_KEXDH_INIT
mpint	e
The server then responds with the following:
byte	SSH_MSG_KEXDH_REPLY
string	server public host key and certificates (K_S)
mpint	f
string	signature of H

Key re-exchange is started by sending an SSH_MSG_KEXINIT packet when not already doing a key exchange (as described in Section 7.1). When this message is received, a party MUST respond with its own SSH_MSG_KEXINIT message, except when the received SSH_MSG_KEXINIT already was a reply. Either party MAY initiate the re-exchange, but roles MUST NOT be changed (i.e., the server remains the server, and the client remains the client).

After the key exchange, the client requests a service. The service is identified by a name. The format of names and procedures for defining new names are defined in [SSH-ARCH] and [SSH-NUMBERS].

If the server rejects the service request, it SHOULD send an appropriate SSH_MSG_DISCONNECT message and MUST disconnect.

If the server supports the service (and permits the client to use it), it MUST respond with the following:
byte	SSH_MSG_SERVICE_ACCEPT
string	service name

Note that after a key exchange with implicit server authentication, the client MUST wait for a response to its service request message before sending any further data.

Either party may send any of the following messages at any time.

11.1. Disconnection Message
This message causes immediate termination of the connection. All implementations MUST be able to process this message; they SHOULD be able to send this message.

11.2. Ignored Data Message
All implementations MUST understand (and ignore) this message at any time (after receiving the identification string).

11.3. Debug Message
All implementations MUST understand this message, but they are allowed to ignore it.

11.4. Reserved Messages
An implementation MUST respond to all unrecognized messages with an SSH_MSG_UNIMPLEMENTED message in the order in which the messages were received. Such messages MUST be otherwise ignored.

[radboud learned model]
KEXINIT, SR_*, UNIMPL, DEBUG, IGNORE, KEX30 / KEXINIT

KEX30 / KEX31+NEWKEYS

NEWKEYS / NO_RESP


[ssh verbose connection log]
OpenSSH_7.6p1, LibreSSL 2.6.2
debug1: Reading configuration data /Users/<user>/.ssh/config
debug1: /Users/<user>/.ssh/config line 2: Applying options for den
debug1: Reading configuration data /etc/ssh/ssh_config
debug1: /etc/ssh/ssh_config line 48: Applying options for *
debug2: ssh_connect_direct: needpriv 0
debug1: Connecting to <domain> port <port>.
debug1: Connection established.
debug1: identity file /Users/<user>/.ssh/id_rsa type 0
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_rsa-cert type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_dsa type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_dsa-cert type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_ecdsa type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_ecdsa-cert type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_ed25519 type -1
debug1: key_load_public: No such file or directory
debug1: identity file /Users/<user>/.ssh/id_ed25519-cert type -1
debug1: Local version string SSH-2.0-OpenSSH_7.6
debug1: Remote protocol version 2.0, remote software version OpenSSH_7.2p2 Ubuntu-4ubuntu2.2
debug1: match: OpenSSH_7.2p2 Ubuntu-4ubuntu2.2 pat OpenSSH* compat 0x04000000
debug3: fd 5 is O_NONBLOCK
debug1: Authenticating to <domain>:<port> as '<user>'
debug3: put_host_port: [<domain>]:<port>
debug3: hostkeys_foreach: reading file "/Users/<user>/.ssh/known_hosts"
debug3: record_hostkey: found key type ECDSA in file /Users/<user>/.ssh/known_hosts:2
debug3: load_hostkeys: loaded 1 keys from [<domain>]:<port>
debug3: order_hostkeyalgs: prefer hostkeyalgs: ecdsa-sha2-nistp256-cert-v01@openssh.com,ecdsa-sha2-nistp384-cert-v01@openssh.com,ecdsa-sha2-nistp521-cert-v01@openssh.com,ecdsa-sha2-nistp256,ecdsa-sha2-nistp384,ecdsa-sha2-nistp521
debug3: send packet: type 20
debug1: SSH2_MSG_KEXINIT sent
debug3: receive packet: type 20
debug1: SSH2_MSG_KEXINIT received
debug2: local client KEXINIT proposal
debug2: KEX algorithms: curve25519-sha256,curve25519-sha256@libssh.org,ecdh-sha2-nistp256,ecdh-sha2-nistp384,ecdh-sha2-nistp521,diffie-hellman-group-exchange-sha256,diffie-hellman-group16-sha512,diffie-hellman-group18-sha512,diffie-hellman-group-exchange-sha1,diffie-hellman-group14-sha256,diffie-hellman-group14-sha1,ext-info-c
debug2: host key algorithms: ecdsa-sha2-nistp256-cert-v01@openssh.com,ecdsa-sha2-nistp384-cert-v01@openssh.com,ecdsa-sha2-nistp521-cert-v01@openssh.com,ecdsa-sha2-nistp256,ecdsa-sha2-nistp384,ecdsa-sha2-nistp521,ssh-ed25519-cert-v01@openssh.com,ssh-rsa-cert-v01@openssh.com,ssh-ed25519,rsa-sha2-512,rsa-sha2-256,ssh-rsa
debug2: ciphers ctos: chacha20-poly1305@openssh.com,aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
debug2: ciphers stoc: chacha20-poly1305@openssh.com,aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
debug2: MACs ctos: umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com,hmac-sha1-etm@openssh.com,umac-64@openssh.com,umac-128@openssh.com,hmac-sha2-256,hmac-sha2-512,hmac-sha1
debug2: MACs stoc: umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com,hmac-sha1-etm@openssh.com,umac-64@openssh.com,umac-128@openssh.com,hmac-sha2-256,hmac-sha2-512,hmac-sha1
debug2: compression ctos: none,zlib@openssh.com,zlib
debug2: compression stoc: none,zlib@openssh.com,zlib
debug2: languages ctos:
debug2: languages stoc:
debug2: first_kex_follows 0
debug2: reserved 0
debug2: peer server KEXINIT proposal
debug2: KEX algorithms: curve25519-sha256@libssh.org,ecdh-sha2-nistp256,ecdh-sha2-nistp384,ecdh-sha2-nistp521,diffie-hellman-group-exchange-sha256,diffie-hellman-group14-sha1
debug2: host key algorithms: ssh-rsa,rsa-sha2-512,rsa-sha2-256,ecdsa-sha2-nistp256,ssh-ed25519
debug2: ciphers ctos: chacha20-poly1305@openssh.com,aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
debug2: ciphers stoc: chacha20-poly1305@openssh.com,aes128-ctr,aes192-ctr,aes256-ctr,aes128-gcm@openssh.com,aes256-gcm@openssh.com
debug2: MACs ctos: umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com,hmac-sha1-etm@openssh.com,umac-64@openssh.com,umac-128@openssh.com,hmac-sha2-256,hmac-sha2-512,hmac-sha1
debug2: MACs stoc: umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256-etm@openssh.com,hmac-sha2-512-etm@openssh.com,hmac-sha1-etm@openssh.com,umac-64@openssh.com,umac-128@openssh.com,hmac-sha2-256,hmac-sha2-512,hmac-sha1
debug2: compression ctos: none,zlib@openssh.com
debug2: compression stoc: none,zlib@openssh.com
debug2: languages ctos:
debug2: languages stoc:
debug2: first_kex_follows 0
debug2: reserved 0
debug1: kex: algorithm: curve25519-sha256@libssh.org
debug1: kex: host key algorithm: ecdsa-sha2-nistp256
debug1: kex: server->client cipher: chacha20-poly1305@openssh.com MAC: <implicit> compression: none
debug1: kex: client->server cipher: chacha20-poly1305@openssh.com MAC: <implicit> compression: none
debug3: send packet: type 30
debug1: expecting SSH2_MSG_KEX_ECDH_REPLY
debug3: receive packet: type 31
debug1: Server host key: ecdsa-sha2-nistp256 SHA256:2BiES0CMfL9ZSgcuCtkc8+l2ppd+Bu/A06JivILAMqc
debug3: put_host_port: [<ip>]:<port>
debug3: put_host_port: [<domain>]:<port>
debug3: hostkeys_foreach: reading file "/Users/<user>/.ssh/known_hosts"
debug3: record_hostkey: found key type ECDSA in file /Users/<user>/.ssh/known_hosts:2
debug3: load_hostkeys: loaded 1 keys from [<domain>]:<port>
debug3: hostkeys_foreach: reading file "/Users/<user>/.ssh/known_hosts"
debug3: record_hostkey: found key type ECDSA in file /Users/<user>/.ssh/known_hosts:2
debug3: load_hostkeys: loaded 1 keys from [<ip>]:<port>
debug1: Host '[<domain>]:<port>' is known and matches the ECDSA host key.
debug1: Found key in /Users/<user>/.ssh/known_hosts:2
debug3: send packet: type 21
debug2: set_newkeys: mode 1
debug1: rekey after 134217728 blocks
debug1: SSH2_MSG_NEWKEYS sent
debug1: expecting SSH2_MSG_NEWKEYS
debug3: receive packet: type 21
debug1: SSH2_MSG_NEWKEYS received
debug2: set_newkeys: mode 0
debug1: rekey after 134217728 blocks
debug2: key: /Users/<user>/.ssh/id_rsa (0x7f7f92c09ed0), agent
debug2: key: /Users/<user>/.ssh/github_rsa (0x7f7f92f00af0), agent
debug2: key: /Users/<user>/.ssh/id_dsa (0x0)
debug2: key: /Users/<user>/.ssh/id_ecdsa (0x0)
debug2: key: /Users/<user>/.ssh/id_ed25519 (0x0)
debug3: send packet: type 5
debug3: receive packet: type 7
debug1: SSH2_MSG_EXT_INFO received
debug1: kex_input_ext_info: server-sig-algs=<rsa-sha2-256,rsa-sha2-512>
debug3: receive packet: type 6
debug2: service_accept: ssh-userauth
debug1: SSH2_MSG_SERVICE_ACCEPT received
debug3: send packet: type 50
debug3: receive packet: type 51
debug1: Authentications that can continue: publickey,password
debug3: start over, passed a different list publickey,password
debug3: preferred publickey,keyboard-interactive,password
debug3: authmethod_lookup publickey
debug3: remaining preferred: keyboard-interactive,password
debug3: authmethod_is_enabled publickey
debug1: Next authentication method: publickey
debug1: Offering public key: RSA SHA256:YiAAZSSXMHcvcEsDhvj8OVUrdT1IyvOuZLBbjIrR5jQ /Users/<user>/.ssh/id_rsa
debug3: send_pubkey_test
debug3: send packet: type 50
debug2: we sent a publickey packet, wait for reply
debug3: receive packet: type 51
debug1: Authentications that can continue: publickey,password
debug1: Offering public key: RSA SHA256:2AJ2BG4o85/BcCo74mu/xZo24OlG7HcXmmCkM3EJogw /Users/<user>/.ssh/github_rsa
debug3: send_pubkey_test
debug3: send packet: type 50
debug2: we sent a publickey packet, wait for reply
debug3: receive packet: type 51
debug1: Authentications that can continue: publickey,password
debug1: Trying private key: /Users/<user>/.ssh/id_dsa
debug3: no such identity: /Users/<user>/.ssh/id_dsa: No such file or directory
debug1: Trying private key: /Users/<user>/.ssh/id_ecdsa
debug3: no such identity: /Users/<user>/.ssh/id_ecdsa: No such file or directory
debug1: Trying private key: /Users/<user>/.ssh/id_ed25519
debug3: no such identity: /Users/<user>/.ssh/id_ed25519: No such file or directory
debug2: we did not send a packet, disable method
debug3: authmethod_lookup password
debug3: remaining preferred: ,password
debug3: authmethod_is_enabled password
debug1: Next authentication method: password
<user>@<domain>'s password:
debug3: send packet: type 50
debug2: we sent a password packet, wait for reply
debug3: receive packet: type 52
debug1: Authentication succeeded (password).
Authenticated to <domain> ([<ip>]:<port>).
debug1: channel 0: new [client-session]
debug3: ssh_session2_open: channel_new: 0
debug2: channel 0: send open
debug3: send packet: type 90
debug1: Requesting no-more-sessions@openssh.com
debug3: send packet: type 80
debug1: Entering interactive session.
debug1: pledge: network
debug3: receive packet: type 80
debug1: client_input_global_request: rtype hostkeys-00@openssh.com want_reply 0
debug3: receive packet: type 91
debug2: channel_input_open_confirmation: channel 0: callback start
debug2: fd 5 setting TCP_NODELAY
debug3: ssh_packet_set_tos: set IP_TOS 0x10
debug2: client_session2_setup: id 0
debug2: channel 0: request pty-req confirm 1
debug3: send packet: type 98
debug1: Sending environment.
debug3: Ignored env TERM_PROGRAM
debug3: Ignored env SHELL
debug3: Ignored env TERM
debug3: Ignored env TMPDIR
debug3: Ignored env Apple_PubSub_Socket_Render
debug3: Ignored env TERM_PROGRAM_VERSION
debug3: Ignored env TERM_SESSION_ID
debug3: Ignored env USER
debug3: Ignored env SSH_AUTH_SOCK
debug3: Ignored env PATH
debug3: Ignored env PWD
debug3: Ignored env XPC_FLAGS
debug3: Ignored env XPC_SERVICE_NAME
debug3: Ignored env SHLVL
debug3: Ignored env HOME
debug3: Ignored env LOGNAME
debug1: Sending env LC_CTYPE = UTF-8
debug2: channel 0: request env confirm 0
debug3: send packet: type 98
debug3: Ignored env SECURITYSESSIONID
debug3: Ignored env OLDPWD
debug3: Ignored env CLICOLOR
debug3: Ignored env VISUAL
debug3: Ignored env EDITOR
debug3: Ignored env COWPATH
debug3: Ignored env PAGER
debug3: Ignored env LESS
debug3: Ignored env LSCOLORS
debug3: Ignored env PROMPT_EOL_MARK
debug1: Sending env LANG = en_US.UTF-8
debug2: channel 0: request env confirm 0
debug3: send packet: type 98
debug1: Sending env LC_ALL = en_US.UTF-8
debug2: channel 0: request env confirm 0
debug3: send packet: type 98
debug3: Ignored env _
debug3: Ignored env __CF_USER_TEXT_ENCODING
debug2: channel 0: request shell confirm 1
debug3: send packet: type 98
debug2: channel_input_open_confirmation: channel 0: callback done
debug2: channel 0: open confirm rwindow 0 rmax 32768
debug3: receive packet: type 99
debug2: channel_input_status_confirm: type 99 id 0
debug2: PTY allocation request accepted on channel 0
debug2: channel 0: rcvd adjust 2097152
debug3: receive packet: type 99
debug2: channel_input_status_confirm: type 99 id 0
debug2: shell request accepted on channel 0
Welcome to elementary OS 0.4.1 Loki (GNU/Linux 4.4.0-64-generic x86_64)

 * Website:  http://elementary.io/

237 packages can be updated.
0 updates are security updates.
